import NetHack.Soko22Hazard87.AndIntroBlocks0213
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro53500 (p : Pattern) (ha : d16667 p = 1) (hb : d198467 p = 1) : d201122 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13160 q = 1) (hb : d198467 q = 1) : d201101 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13160, d201101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13160, d201101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53480 q ha hb
  have h2 (q : Pattern) (ha : d9814 q = 1) (hb : d198467 q = 1) : d200928 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9814, d200928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53480 q ha hb
    | true =>
      simp only [d9814, d200928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13161 q = 1) (hb : d198467 q = 1) : d201102 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13161, d201102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13161, d201102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9816 q = 1) (hb : d198467 q = 1) : d200929 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9816, d200929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9816, d200929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13162 q = 1) (hb : d198467 q = 1) : d201103 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13162, d201103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13162, d201103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13163 q = 1) (hb : d198467 q = 1) : d201104 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13163, d201104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13163, d201104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15004 q = 1) (hb : d198467 q = 1) : d201112 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15004, d201112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15004, d201112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53450 q ha hb
  have h8 (q : Pattern) (ha : d9800 q = 1) (hb : d198467 q = 1) : d200933 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, d200933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53450 q ha hb
    | true =>
      simp only [d9800, d200933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15005 q = 1) (hb : d198467 q = 1) : d201113 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15005, d201113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15005, d201113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9802 q = 1) (hb : d198467 q = 1) : d200934 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9802, d200934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9802, d200934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d15006 q = 1) (hb : d198467 q = 1) : d201114 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15006, d201114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15006, d201114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d15007 q = 1) (hb : d198467 q = 1) : d201115 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15007, d201115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15007, d201115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d16666 q = 1) (hb : d198467 q = 1) : d201116 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16666, d201116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16666, d201116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15008 q = 1) (hb : d198467 q = 1) : d201121 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15008, d201121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15008, d201121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d16667 q = 1) (hb : d198467 q = 1) : d201122 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16667, d201122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16667, d201122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro53501 (p : Pattern) (ha : d16681 p = 1) (hb : d198467 p = 1) : d201138 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16663 q = 1) (hb : d198467 q = 1) : d201118 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16663, d201118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53498 q ha hb
    | true =>
      simp only [d16663, d201118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53499 q ha hb
  have h2 (q : Pattern) (ha : d16664 q = 1) (hb : d198467 q = 1) : d201119 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16664, d201119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16664, d201119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16665 q = 1) (hb : d198467 q = 1) : d201120 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16665, d201120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16665, d201120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16668 q = 1) (hb : d198467 q = 1) : d201123 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16668, d201123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53499 q ha hb
    | true =>
      simp only [d16668, d201123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53500 q ha hb
  have h5 (q : Pattern) (ha : d16669 q = 1) (hb : d198467 q = 1) : d201124 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16669, d201124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16669, d201124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16670 q = 1) (hb : d198467 q = 1) : d201125 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16670, d201125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16670, d201125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16671 q = 1) (hb : d198467 q = 1) : d201126 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16671, d201126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16671, d201126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16673 q = 1) (hb : d198467 q = 1) : d201129 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16673, d201129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53499 q ha hb
    | true =>
      simp only [d16673, d201129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53468 q ha hb
  have h9 (q : Pattern) (ha : d16674 q = 1) (hb : d198467 q = 1) : d201130 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16674, d201130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16674, d201130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16675 q = 1) (hb : d198467 q = 1) : d201131 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16675, d201131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16675, d201131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16676 q = 1) (hb : d198467 q = 1) : d201133 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16676, d201133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53468 q ha hb
    | true =>
      simp only [d16676, d201133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53497 q ha hb
  have h12 (q : Pattern) (ha : d16677 q = 1) (hb : d198467 q = 1) : d201134 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16677, d201134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16677, d201134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16678 q = 1) (hb : d198467 q = 1) : d201135 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16678, d201135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16678, d201135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d16679 q = 1) (hb : d198467 q = 1) : d201136 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16679, d201136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16679, d201136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16680 q = 1) (hb : d198467 q = 1) : d201137 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16680, d201137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16680, d201137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16681 q = 1) (hb : d198467 q = 1) : d201138 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16681, d201138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d16681, d201138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro53502 (p : Pattern) (ha : d16686 p = 1) (hb : d198467 p = 1) : d201143 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16673 q = 1) (hb : d198467 q = 1) : d201129 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16673, d201129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53499 q ha hb
    | true =>
      simp only [d16673, d201129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53468 q ha hb
  have h2 (q : Pattern) (ha : d16674 q = 1) (hb : d198467 q = 1) : d201130 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16674, d201130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16674, d201130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16675 q = 1) (hb : d198467 q = 1) : d201131 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16675, d201131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16675, d201131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16676 q = 1) (hb : d198467 q = 1) : d201133 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16676, d201133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53468 q ha hb
    | true =>
      simp only [d16676, d201133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53497 q ha hb
  have h5 (q : Pattern) (ha : d16677 q = 1) (hb : d198467 q = 1) : d201134 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16677, d201134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16677, d201134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16678 q = 1) (hb : d198467 q = 1) : d201135 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16678, d201135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16678, d201135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16679 q = 1) (hb : d198467 q = 1) : d201136 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16679, d201136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16679, d201136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16684 q = 1) (hb : d198467 q = 1) : d201141 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16684, d201141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16684, d201141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16685 q = 1) (hb : d198467 q = 1) : d201142 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16685, d201142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16685, d201142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16686 q = 1) (hb : d198467 q = 1) : d201143 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16686, d201143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16686, d201143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro53503 (p : Pattern) (ha : d16692 p = 1) (hb : d198467 p = 1) : d201149 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16682 q = 1) (hb : d198467 q = 1) : d201139 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16682, d201139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53501 q ha hb
    | true =>
      simp only [d16682, d201139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16683 q = 1) (hb : d198467 q = 1) : d201140 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16683, d201140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16683, d201140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16687 q = 1) (hb : d198467 q = 1) : d201144 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16687, d201144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53502 q ha hb
    | true =>
      simp only [d16687, d201144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16688 q = 1) (hb : d198467 q = 1) : d201145 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16688, d201145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16688, d201145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16689 q = 1) (hb : d198467 q = 1) : d201146 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16689, d201146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16689, d201146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16690 q = 1) (hb : d198467 q = 1) : d201147 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16690, d201147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16690, d201147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16691 q = 1) (hb : d198467 q = 1) : d201148 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16691, d201148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16691, d201148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16692 q = 1) (hb : d198467 q = 1) : d201149 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16692, d201149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16692, d201149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro53504 (p : Pattern) (ha : d16704 p = 1) (hb : d198467 p = 1) : d201157 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16687 q = 1) (hb : d198467 q = 1) : d201144 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16687, d201144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53502 q ha hb
    | true =>
      simp only [d16687, d201144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16688 q = 1) (hb : d198467 q = 1) : d201145 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16688, d201145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16688, d201145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16699 q = 1) (hb : d198467 q = 1) : d201152 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16699, d201152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53469 q ha hb
    | true =>
      simp only [d16699, d201152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16700 q = 1) (hb : d198467 q = 1) : d201153 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16700, d201153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16700, d201153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16701 q = 1) (hb : d198467 q = 1) : d201154 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16701, d201154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16701, d201154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16702 q = 1) (hb : d198467 q = 1) : d201155 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16702, d201155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16702, d201155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16703 q = 1) (hb : d198467 q = 1) : d201156 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16703, d201156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16703, d201156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16704 q = 1) (hb : d198467 q = 1) : d201157 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16704, d201157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16704, d201157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro53505 (p : Pattern) (ha : d13190 p = 1) (hb : d198467 p = 1) : d201160 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1391 q = 1) (hb : d198467 q = 1) : d201112 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1391, d201112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1391, d201112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53445 q ha hb
  have h2 (q : Pattern) (ha : d1121 q = 1) (hb : d198467 q = 1) : d200933 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d200933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53445 q ha hb
    | true =>
      simp only [d1121, d200933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1392 q = 1) (hb : d198467 q = 1) : d201113 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1392, d201113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1392, d201113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1122 q = 1) (hb : d198467 q = 1) : d200934 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d200934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1122, d200934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1393 q = 1) (hb : d198467 q = 1) : d201114 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1393, d201114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1393, d201114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1394 q = 1) (hb : d198467 q = 1) : d201115 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1394, d201115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1394, d201115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1400 q = 1) (hb : d198467 q = 1) : d201121 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1400, d201121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1400, d201121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13190 q = 1) (hb : d198467 q = 1) : d201160 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13190, d201160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13190, d201160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro53506 (p : Pattern) (ha : d16748 p = 1) (hb : d198467 p = 1) : d201166 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16673 q = 1) (hb : d198467 q = 1) : d201129 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16673, d201129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53499 q ha hb
    | true =>
      simp only [d16673, d201129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53468 q ha hb
  have h2 (q : Pattern) (ha : d16674 q = 1) (hb : d198467 q = 1) : d201130 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16674, d201130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16674, d201130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16675 q = 1) (hb : d198467 q = 1) : d201131 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16675, d201131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16675, d201131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16676 q = 1) (hb : d198467 q = 1) : d201133 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16676, d201133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53468 q ha hb
    | true =>
      simp only [d16676, d201133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53497 q ha hb
  have h5 (q : Pattern) (ha : d16677 q = 1) (hb : d198467 q = 1) : d201134 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16677, d201134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16677, d201134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16678 q = 1) (hb : d198467 q = 1) : d201135 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16678, d201135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16678, d201135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16679 q = 1) (hb : d198467 q = 1) : d201136 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16679, d201136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16679, d201136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16743 q = 1) (hb : d198467 q = 1) : d201161 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16743, d201161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53468 q ha hb
    | true =>
      simp only [d16743, d201161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53505 q ha hb
  have h9 (q : Pattern) (ha : d16744 q = 1) (hb : d198467 q = 1) : d201162 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16744, d201162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16744, d201162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16745 q = 1) (hb : d198467 q = 1) : d201163 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16745, d201163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16745, d201163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16746 q = 1) (hb : d198467 q = 1) : d201164 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16746, d201164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16746, d201164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d16747 q = 1) (hb : d198467 q = 1) : d201165 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16747, d201165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16747, d201165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16748 q = 1) (hb : d198467 q = 1) : d201166 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16748, d201166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d16748, d201166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro53507 (p : Pattern) (ha : d16754 p = 1) (hb : d198467 p = 1) : d201172 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16749 q = 1) (hb : d198467 q = 1) : d201167 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16749, d201167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53506 q ha hb
    | true =>
      simp only [d16749, d201167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16750 q = 1) (hb : d198467 q = 1) : d201168 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16750, d201168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16750, d201168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16751 q = 1) (hb : d198467 q = 1) : d201169 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16751, d201169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16751, d201169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16752 q = 1) (hb : d198467 q = 1) : d201170 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16752, d201170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16752, d201170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16753 q = 1) (hb : d198467 q = 1) : d201171 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16753, d201171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16753, d201171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16754 q = 1) (hb : d198467 q = 1) : d201172 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16754, d201172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16754, d201172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53508 (p : Pattern) (ha : d128337 p = 1) (hb : d198467 p = 1) : d201178 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16705 q = 1) (hb : d198467 q = 1) : d201158 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16705, d201158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53503 q ha hb
    | true =>
      simp only [d16705, d201158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53504 q ha hb
  have h2 (q : Pattern) (ha : d128333 q = 1) (hb : d198467 q = 1) : d201159 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128333, d201159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128333, d201159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16755 q = 1) (hb : d198467 q = 1) : d201173 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16755, d201173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53507 q ha hb
    | true =>
      simp only [d16755, d201173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16756 q = 1) (hb : d198467 q = 1) : d201174 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16756, d201174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16756, d201174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128334 q = 1) (hb : d198467 q = 1) : d201175 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128334, d201175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128334, d201175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128335 q = 1) (hb : d198467 q = 1) : d201176 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128335, d201176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128335, d201176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128336 q = 1) (hb : d198467 q = 1) : d201177 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128336, d201177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128336, d201177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128337 q = 1) (hb : d198467 q = 1) : d201178 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128337, d201178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128337, d201178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53509 (p : Pattern) (ha : d128343 p = 1) (hb : d198467 p = 1) : d201195 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16477 q = 1) (hb : d198467 q = 1) : d200973 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16477, d200973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16477, d200973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53458 q ha hb
  have h2 (q : Pattern) (ha : d16478 q = 1) (hb : d198467 q = 1) : d200974 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16478, d200974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16478, d200974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16487 q = 1) (hb : d198467 q = 1) : d200983 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16487, d200983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53458 q ha hb
    | true =>
      simp only [d16487, d200983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53461 q ha hb
  have h4 (q : Pattern) (ha : d16488 q = 1) (hb : d198467 q = 1) : d200984 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16488, d200984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16488, d200984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16489 q = 1) (hb : d198467 q = 1) : d200985 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d16489, d200985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16489, d200985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128321 q = 1) (hb : d198467 q = 1) : d201069 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128321, d201069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53487 q ha hb
    | true =>
      simp only [d128321, d201069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53495 q ha hb
  have h7 (q : Pattern) (ha : d16635 q = 1) (hb : d198467 q = 1) : d201082 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16635, d201082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53464 q ha hb
    | true =>
      simp only [d16635, d201082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53465 q ha hb
  have h8 (q : Pattern) (ha : d128322 q = 1) (hb : d198467 q = 1) : d201083 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128322, d201083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128322, d201083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128323 q = 1) (hb : d198467 q = 1) : d201084 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128323, d201084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128323, d201084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d128324 q = 1) (hb : d198467 q = 1) : d201085 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128324, d201085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128324, d201085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128328 q = 1) (hb : d198467 q = 1) : d201089 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128328, d201089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128328, d201089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53496 q ha hb
  have h12 (q : Pattern) (ha : d16644 q = 1) (hb : d198467 q = 1) : d201091 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16644, d201091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16644, d201091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53466 q ha hb
  have h13 (q : Pattern) (ha : d128329 q = 1) (hb : d198467 q = 1) : d201092 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128329, d201092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128329, d201092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128330 q = 1) (hb : d198467 q = 1) : d201093 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128330, d201093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128330, d201093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d128331 q = 1) (hb : d198467 q = 1) : d201094 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128331, d201094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128331, d201094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d128332 q = 1) (hb : d198467 q = 1) : d201095 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128332, d201095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128332, d201095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d128338 q = 1) (hb : d198467 q = 1) : d201179 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128338, d201179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128338, d201179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53508 q ha hb
  have h18 (q : Pattern) (ha : d16772 q = 1) (hb : d198467 q = 1) : d201190 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16772, d201190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16772, d201190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53471 q ha hb
  have h19 (q : Pattern) (ha : d128339 q = 1) (hb : d198467 q = 1) : d201191 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128339, d201191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128339, d201191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d128340 q = 1) (hb : d198467 q = 1) : d201192 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128340, d201192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d128340, d201192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d128341 q = 1) (hb : d198467 q = 1) : d201193 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128341, d201193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d128341, d201193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d128342 q = 1) (hb : d198467 q = 1) : d201194 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128342, d201194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128342, d201194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d128343 q = 1) (hb : d198467 q = 1) : d201195 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128343, d201195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128343, d201195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro53510 (p : Pattern) (ha : d128349 p = 1) (hb : d198467 p = 1) : d201201 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128344 q = 1) (hb : d198467 q = 1) : d201196 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128344, d201196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128344, d201196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53509 q ha hb
  have h2 (q : Pattern) (ha : d128345 q = 1) (hb : d198467 q = 1) : d201197 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128345, d201197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128345, d201197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128346 q = 1) (hb : d198467 q = 1) : d201198 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128346, d201198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128346, d201198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128347 q = 1) (hb : d198467 q = 1) : d201199 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128347, d201199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128347, d201199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128348 q = 1) (hb : d198467 q = 1) : d201200 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128348, d201200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128348, d201200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128349 q = 1) (hb : d198467 q = 1) : d201201 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128349, d201201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128349, d201201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53511 (p : Pattern) (ha : d5133 p = 1) (hb : d198467 p = 1) : d201211 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1545 q = 1) : d1545 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5124 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5125 q = 1) (hb : d152852 q = 1) : d26558 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5125, d152852, d26558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5125, d152852, d26558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d1550 q = 1) : d1550 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1565 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1566 q = 1) (hb : d152852 q = 1) : d10081 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1566, d152852, d10081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d1566, d152852, d10081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d5126 q = 1) (hb : d152852 q = 1) : d26572 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5126, d26572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5126, d26572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d5127 q = 1) (hb : d152852 q = 1) : d26573 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5127, d26573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5127, d26573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d5132 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d5133 q = 1) (hb : d198467 q = 1) : d201211 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d5133, d198467, d201211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5133, d198467, d201211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro53512 (p : Pattern) (ha : d15166 p = 1) (hb : d198467 p = 1) : d201224 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5134 q = 1) (hb : d198467 q = 1) : d201212 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5134, d201212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53511 q ha hb
    | true =>
      simp only [d5134, d201212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5135 q = 1) (hb : d198467 q = 1) : d201213 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5135, d201213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5135, d201213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5136 q = 1) (hb : d198467 q = 1) : d201214 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5136, d201214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5136, d201214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5137 q = 1) (hb : d198467 q = 1) : d201215 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5137, d201215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5137, d201215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5138 q = 1) (hb : d198467 q = 1) : d201219 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5138, d201219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5138, d201219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15165 q = 1) (hb : d198467 q = 1) : d15165 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15166 q = 1) (hb : d198467 q = 1) : d201224 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15166, d201224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15166, d201224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro53513 (p : Pattern) (ha : d1581 p = 1) (hb : d198467 p = 1) : d201211 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1545 q = 1) : d1545 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1561 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1562 q = 1) (hb : d152852 q = 1) : d26558 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1562, d152852, d26558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1562, d152852, d26558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d1550 q = 1) : d1550 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1565 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1566 q = 1) (hb : d152852 q = 1) : d10081 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1566, d152852, d10081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d1566, d152852, d10081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1567 q = 1) (hb : d152852 q = 1) : d26572 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1567, d26572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1567, d26572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1568 q = 1) (hb : d152852 q = 1) : d26573 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1568, d26573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1568, d26573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d1580 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d1581 q = 1) (hb : d198467 q = 1) : d201211 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d1581, d198467, d201211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1581, d198467, d201211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro53514 (p : Pattern) (ha : d15171 p = 1) (hb : d198467 p = 1) : d201224 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1582 q = 1) (hb : d198467 q = 1) : d201212 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d201212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53513 q ha hb
    | true =>
      simp only [d1582, d201212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1583 q = 1) (hb : d198467 q = 1) : d201213 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d201213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1583, d201213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1584 q = 1) (hb : d198467 q = 1) : d201214 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1584, d201214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1584, d201214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1585 q = 1) (hb : d198467 q = 1) : d201215 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1585, d201215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1585, d201215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1588 q = 1) (hb : d198467 q = 1) : d201219 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1588, d201219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1588, d201219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15165 q = 1) (hb : d198467 q = 1) : d15165 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15171 q = 1) (hb : d198467 q = 1) : d201224 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15171, d201224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15171, d201224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro53515 (p : Pattern) (ha : d1554 p = 1) (hb : d198467 p = 1) : d201003 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1201 q = 1) : d1201 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1529 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1530 q = 1) (hb : d152852 q = 1) : d10042 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1530, d152852, d10042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1530, d152852, d10042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d1205 q = 1) : d1205 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1535 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1536 q = 1) (hb : d152852 q = 1) : d26185 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1536, d152852, d26185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d1536, d152852, d26185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1537 q = 1) (hb : d152852 q = 1) : d26186 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1537, d26186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1537, d26186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1538 q = 1) (hb : d152852 q = 1) : d26187 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1538, d26187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1538, d26187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d1553 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d1554 q = 1) (hb : d198467 q = 1) : d201003 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d1554, d198467, d201003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1554, d198467, d201003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro53516 (p : Pattern) (ha : d10062 p = 1) (hb : d198467 p = 1) : d22225 p = 1 := by
  have h0 (q : Pattern) (ha : d10053 q = 1) (hb : d152852 q = 1) : d10053 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10061 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10062 q = 1) (hb : d198467 q = 1) : d22225 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d10062, d198467, d22225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10062, d198467, d22225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro53517 (p : Pattern) (ha : d10073 p = 1) (hb : d198467 p = 1) : d201205 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1529 q = 1) : d1529 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1545 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1546 q = 1) (hb : d152852 q = 1) : d10051 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1546, d152852, d10051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1546, d152852, d10051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d1535 q = 1) : d1535 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1550 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1551 q = 1) (hb : d152852 q = 1) : d26555 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1551, d152852, d26555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d1551, d152852, d26555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1552 q = 1) (hb : d152852 q = 1) : d26556 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1552, d26556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1552, d26556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1553 q = 1) (hb : d152852 q = 1) : d26557 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1553, d26557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1553, d26557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10061 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d10073 q = 1) (hb : d198467 q = 1) : d201205 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d10073, d198467, d201205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10073, d198467, d201205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro53518 (p : Pattern) (ha : d10084 p = 1) (hb : d198467 p = 1) : d201211 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1545 q = 1) : d1545 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10058 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10080 q = 1) (hb : d152852 q = 1) : d26558 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10080, d152852, d26558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d10080, d152852, d26558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d10081 q = 1) (hb : d152852 q = 1) : d10081 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10082 q = 1) (hb : d152852 q = 1) : d26572 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10082, d26572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10082, d26572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10083 q = 1) (hb : d152852 q = 1) : d26573 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10083, d26573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10083, d26573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d5132 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10084 q = 1) (hb : d198467 q = 1) : d201211 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d10084, d198467, d201211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10084, d198467, d201211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro53519 (p : Pattern) (ha : d16791 p = 1) (hb : d198467 p = 1) : d201217 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1555 q = 1) (hb : d198467 q = 1) : d201004 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1555, d201004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53515 q ha hb
    | true =>
      simp only [d1555, d201004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1556 q = 1) (hb : d198467 q = 1) : d201005 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1556, d201005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1556, d201005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1557 q = 1) (hb : d198467 q = 1) : d201006 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1557, d201006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1557, d201006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1558 q = 1) (hb : d198467 q = 1) : d201007 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1558, d201007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1558, d201007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10074 q = 1) (hb : d198467 q = 1) : d201206 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10074, d201206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53517 q ha hb
    | true =>
      simp only [d10074, d201206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10076 q = 1) (hb : d198467 q = 1) : d201207 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10076, d201207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10076, d201207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16787 q = 1) (hb : d198467 q = 1) : d201208 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16787, d201208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16787, d201208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16788 q = 1) (hb : d198467 q = 1) : d201209 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16788, d201209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16788, d201209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16789 q = 1) (hb : d198467 q = 1) : d201210 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16789, d201210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16789, d201210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10063 q = 1) (hb : d198467 q = 1) : d22226 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10063, d22226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53516 q ha hb
    | true =>
      simp only [d10063, d22226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d10065 q = 1) (hb : d198467 q = 1) : d22227 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10065, d22227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10065, d22227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15151 q = 1) (hb : d198467 q = 1) : d22228 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15151, d22228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15151, d22228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15152 q = 1) (hb : d198467 q = 1) : d22229 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15152, d22229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15152, d22229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d10085 q = 1) (hb : d198467 q = 1) : d201212 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d201212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53518 q ha hb
    | true =>
      simp only [d10085, d201212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d10087 q = 1) (hb : d198467 q = 1) : d201213 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10087, d201213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10087, d201213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d15156 q = 1) (hb : d198467 q = 1) : d201214 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15156, d201214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15156, d201214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d15157 q = 1) (hb : d198467 q = 1) : d201215 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15157, d201215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d15157, d201215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d16790 q = 1) (hb : d198467 q = 1) : d201216 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16790, d201216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16790, d201216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16791 q = 1) (hb : d198467 q = 1) : d201217 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16791, d201217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16791, d201217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro53520 (p : Pattern) (ha : d1569 p = 1) (hb : d198467 p = 1) : d201205 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1529 q = 1) : d1529 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1545 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1546 q = 1) (hb : d152852 q = 1) : d10051 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1546, d152852, d10051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1546, d152852, d10051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d1535 q = 1) : d1535 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1550 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1551 q = 1) (hb : d152852 q = 1) : d26555 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1551, d152852, d26555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d1551, d152852, d26555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1552 q = 1) (hb : d152852 q = 1) : d26556 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1552, d26556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1552, d26556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1553 q = 1) (hb : d152852 q = 1) : d26557 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1553, d26557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1553, d26557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d1568 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d1569 q = 1) (hb : d198467 q = 1) : d201205 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d1569, d198467, d201205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1569, d198467, d201205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro53521 (p : Pattern) (ha : d10114 p = 1) (hb : d198467 p = 1) : d201211 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1545 q = 1) : d1545 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1561 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1562 q = 1) (hb : d152852 q = 1) : d26558 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1562, d152852, d26558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1562, d152852, d26558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d1550 q = 1) : d1550 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1565 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1566 q = 1) (hb : d152852 q = 1) : d10081 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1566, d152852, d10081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d1566, d152852, d10081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1567 q = 1) (hb : d152852 q = 1) : d26572 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1567, d26572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1567, d26572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1568 q = 1) (hb : d152852 q = 1) : d26573 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1568, d26573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1568, d26573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d5132 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d10114 q = 1) (hb : d198467 q = 1) : d201211 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d10114, d198467, d201211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10114, d198467, d201211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro53522 (p : Pattern) (ha : d16795 p = 1) (hb : d198467 p = 1) : d201220 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1570 q = 1) (hb : d198467 q = 1) : d201206 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d201206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53520 q ha hb
    | true =>
      simp only [d1570, d201206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1571 q = 1) (hb : d198467 q = 1) : d201207 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d201207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1571, d201207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1572 q = 1) (hb : d198467 q = 1) : d201208 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1572, d201208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1572, d201208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1573 q = 1) (hb : d198467 q = 1) : d201209 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1573, d201209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1573, d201209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10115 q = 1) (hb : d198467 q = 1) : d201212 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10115, d201212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53521 q ha hb
    | true =>
      simp only [d10115, d201212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10117 q = 1) (hb : d198467 q = 1) : d201213 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10117, d201213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10117, d201213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16792 q = 1) (hb : d198467 q = 1) : d201214 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16792, d201214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16792, d201214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16793 q = 1) (hb : d198467 q = 1) : d201215 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16793, d201215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16793, d201215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16794 q = 1) (hb : d198467 q = 1) : d201218 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16794, d201218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16794, d201218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10085 q = 1) (hb : d198467 q = 1) : d201212 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d201212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53518 q ha hb
    | true =>
      simp only [d10085, d201212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d10087 q = 1) (hb : d198467 q = 1) : d201213 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10087, d201213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10087, d201213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15156 q = 1) (hb : d198467 q = 1) : d201214 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15156, d201214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15156, d201214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15157 q = 1) (hb : d198467 q = 1) : d201215 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15157, d201215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15157, d201215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d15158 q = 1) (hb : d198467 q = 1) : d201219 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15158, d201219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15158, d201219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d16795 q = 1) (hb : d198467 q = 1) : d201220 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16795, d201220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16795, d201220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro53523 (p : Pattern) (ha : d16808 p = 1) (hb : d198467 p = 1) : d201231 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16796 q = 1) (hb : d198467 q = 1) : d201221 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16796, d201221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53519 q ha hb
    | true =>
      simp only [d16796, d201221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53522 q ha hb
  have h2 (q : Pattern) (ha : d16797 q = 1) (hb : d198467 q = 1) : d201222 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16797, d201222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16797, d201222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16798 q = 1) (hb : d198467 q = 1) : d201223 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16798, d201223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16798, d201223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16799 q = 1) (hb : d198467 q = 1) : d201225 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16799, d201225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53522 q ha hb
    | true =>
      simp only [d16799, d201225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53512 q ha hb
  have h5 (q : Pattern) (ha : d16800 q = 1) (hb : d198467 q = 1) : d201226 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16800, d201226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16800, d201226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16801 q = 1) (hb : d198467 q = 1) : d201227 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16801, d201227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16801, d201227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16802 q = 1) (hb : d198467 q = 1) : d201228 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16802, d201228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16802, d201228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16803 q = 1) (hb : d198467 q = 1) : d201225 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16803, d201225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53522 q ha hb
    | true =>
      simp only [d16803, d201225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53514 q ha hb
  have h9 (q : Pattern) (ha : d16804 q = 1) (hb : d198467 q = 1) : d201226 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16804, d201226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16804, d201226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16805 q = 1) (hb : d198467 q = 1) : d201227 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16805, d201227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16805, d201227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16806 q = 1) (hb : d198467 q = 1) : d201229 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16806, d201229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16806, d201229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d16807 q = 1) (hb : d198467 q = 1) : d201230 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16807, d201230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16807, d201230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16808 q = 1) (hb : d198467 q = 1) : d201231 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16808, d201231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d16808, d201231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro53524 (p : Pattern) (ha : d16812 p = 1) (hb : d198467 p = 1) : d201235 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16803 q = 1) (hb : d198467 q = 1) : d201225 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16803, d201225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53522 q ha hb
    | true =>
      simp only [d16803, d201225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53514 q ha hb
  have h2 (q : Pattern) (ha : d16804 q = 1) (hb : d198467 q = 1) : d201226 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16804, d201226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16804, d201226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16805 q = 1) (hb : d198467 q = 1) : d201227 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16805, d201227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16805, d201227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16806 q = 1) (hb : d198467 q = 1) : d201229 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16806, d201229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16806, d201229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16811 q = 1) (hb : d198467 q = 1) : d201234 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16811, d201234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16811, d201234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16812 q = 1) (hb : d198467 q = 1) : d201235 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16812, d201235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16812, d201235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53525 (p : Pattern) (ha : d16818 p = 1) (hb : d198467 p = 1) : d201241 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16809 q = 1) (hb : d198467 q = 1) : d201232 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16809, d201232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53523 q ha hb
    | true =>
      simp only [d16809, d201232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16810 q = 1) (hb : d198467 q = 1) : d201233 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16810, d201233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16810, d201233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16813 q = 1) (hb : d198467 q = 1) : d201236 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d201236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53524 q ha hb
    | true =>
      simp only [d16813, d201236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16814 q = 1) (hb : d198467 q = 1) : d201237 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d201237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d201237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16815 q = 1) (hb : d198467 q = 1) : d201238 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16815, d201238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16815, d201238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16816 q = 1) (hb : d198467 q = 1) : d201239 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16816, d201239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16816, d201239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16817 q = 1) (hb : d198467 q = 1) : d201240 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16817, d201240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16817, d201240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16818 q = 1) (hb : d198467 q = 1) : d201241 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16818, d201241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16818, d201241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53526 (p : Pattern) (ha : d16822 p = 1) (hb : d198467 p = 1) : d201245 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16813 q = 1) (hb : d198467 q = 1) : d201236 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d201236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53524 q ha hb
    | true =>
      simp only [d16813, d201236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16814 q = 1) (hb : d198467 q = 1) : d201237 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d201237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d201237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16819 q = 1) (hb : d198467 q = 1) : d201242 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16819, d201242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16819, d201242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16820 q = 1) (hb : d198467 q = 1) : d201243 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16820, d201243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16820, d201243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16821 q = 1) (hb : d198467 q = 1) : d201244 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16821, d201244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16821, d201244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16822 q = 1) (hb : d198467 q = 1) : d201245 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16822, d201245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16822, d201245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53527 (p : Pattern) (ha : d16828 p = 1) (hb : d198467 p = 1) : d201251 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16823 q = 1) (hb : d198467 q = 1) : d201246 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16823, d201246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53525 q ha hb
    | true =>
      simp only [d16823, d201246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53526 q ha hb
  have h2 (q : Pattern) (ha : d16824 q = 1) (hb : d198467 q = 1) : d201247 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16824, d201247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16824, d201247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16825 q = 1) (hb : d198467 q = 1) : d201248 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16825, d201248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16825, d201248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16826 q = 1) (hb : d198467 q = 1) : d201249 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16826, d201249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16826, d201249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16827 q = 1) (hb : d198467 q = 1) : d201250 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16827, d201250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16827, d201250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16828 q = 1) (hb : d198467 q = 1) : d201251 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16828, d201251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16828, d201251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53528 (p : Pattern) (ha : d16831 p = 1) (hb : d198467 p = 1) : d201254 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16809 q = 1) (hb : d198467 q = 1) : d201232 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16809, d201232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53523 q ha hb
    | true =>
      simp only [d16809, d201232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16810 q = 1) (hb : d198467 q = 1) : d201233 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16810, d201233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16810, d201233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16813 q = 1) (hb : d198467 q = 1) : d201236 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d201236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53524 q ha hb
    | true =>
      simp only [d16813, d201236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16814 q = 1) (hb : d198467 q = 1) : d201237 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d201237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d201237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16815 q = 1) (hb : d198467 q = 1) : d201238 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16815, d201238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16815, d201238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16816 q = 1) (hb : d198467 q = 1) : d201239 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16816, d201239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16816, d201239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16817 q = 1) (hb : d198467 q = 1) : d201240 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16817, d201240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16817, d201240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16831 q = 1) (hb : d198467 q = 1) : d201254 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16831, d201254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16831, d201254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro53529 (p : Pattern) (ha : d16832 p = 1) (hb : d198467 p = 1) : d201255 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16813 q = 1) (hb : d198467 q = 1) : d201236 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d201236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53524 q ha hb
    | true =>
      simp only [d16813, d201236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16814 q = 1) (hb : d198467 q = 1) : d201237 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d201237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d201237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16819 q = 1) (hb : d198467 q = 1) : d201242 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16819, d201242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16819, d201242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16820 q = 1) (hb : d198467 q = 1) : d201243 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16820, d201243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16820, d201243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16821 q = 1) (hb : d198467 q = 1) : d201244 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16821, d201244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16821, d201244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16832 q = 1) (hb : d198467 q = 1) : d201255 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16832, d201255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16832, d201255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53530 (p : Pattern) (ha : d16838 p = 1) (hb : d198467 p = 1) : d201261 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16823 q = 1) (hb : d198467 q = 1) : d201246 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16823, d201246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53525 q ha hb
    | true =>
      simp only [d16823, d201246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53526 q ha hb
  have h2 (q : Pattern) (ha : d16824 q = 1) (hb : d198467 q = 1) : d201247 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16824, d201247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16824, d201247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16825 q = 1) (hb : d198467 q = 1) : d201248 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16825, d201248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16825, d201248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16826 q = 1) (hb : d198467 q = 1) : d201249 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16826, d201249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16826, d201249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16827 q = 1) (hb : d198467 q = 1) : d201250 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16827, d201250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16827, d201250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16833 q = 1) (hb : d198467 q = 1) : d201256 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16833, d201256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53528 q ha hb
    | true =>
      simp only [d16833, d201256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53529 q ha hb
  have h7 (q : Pattern) (ha : d16834 q = 1) (hb : d198467 q = 1) : d201257 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16834, d201257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16834, d201257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16835 q = 1) (hb : d198467 q = 1) : d201258 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16835, d201258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16835, d201258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16836 q = 1) (hb : d198467 q = 1) : d201259 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16836, d201259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16836, d201259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16837 q = 1) (hb : d198467 q = 1) : d201260 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16837, d201260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16837, d201260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16838 q = 1) (hb : d198467 q = 1) : d201261 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16838, d201261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16838, d201261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro53531 (p : Pattern) (ha : d16879 p = 1) (hb : d198467 p = 1) : d201231 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16796 q = 1) (hb : d198467 q = 1) : d201221 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16796, d201221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53519 q ha hb
    | true =>
      simp only [d16796, d201221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53522 q ha hb
  have h2 (q : Pattern) (ha : d16797 q = 1) (hb : d198467 q = 1) : d201222 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16797, d201222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16797, d201222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16798 q = 1) (hb : d198467 q = 1) : d201223 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16798, d201223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16798, d201223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16799 q = 1) (hb : d198467 q = 1) : d201225 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16799, d201225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53522 q ha hb
    | true =>
      simp only [d16799, d201225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53512 q ha hb
  have h5 (q : Pattern) (ha : d16800 q = 1) (hb : d198467 q = 1) : d201226 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16800, d201226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16800, d201226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16801 q = 1) (hb : d198467 q = 1) : d201227 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16801, d201227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16801, d201227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16802 q = 1) (hb : d198467 q = 1) : d201228 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16802, d201228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16802, d201228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16877 q = 1) (hb : d198467 q = 1) : d201229 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16877, d201229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16877, d201229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16878 q = 1) (hb : d198467 q = 1) : d201230 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16878, d201230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16878, d201230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16879 q = 1) (hb : d198467 q = 1) : d201231 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16879, d201231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16879, d201231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro53532 (p : Pattern) (ha : d16889 p = 1) (hb : d198467 p = 1) : d201241 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16880 q = 1) (hb : d198467 q = 1) : d201232 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16880, d201232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53531 q ha hb
    | true =>
      simp only [d16880, d201232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16881 q = 1) (hb : d198467 q = 1) : d201233 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16881, d201233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16881, d201233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16813 q = 1) (hb : d198467 q = 1) : d201236 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d201236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53524 q ha hb
    | true =>
      simp only [d16813, d201236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16814 q = 1) (hb : d198467 q = 1) : d201237 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d201237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d201237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16886 q = 1) (hb : d198467 q = 1) : d201238 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16886, d201238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16886, d201238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16887 q = 1) (hb : d198467 q = 1) : d201239 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16887, d201239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16887, d201239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16888 q = 1) (hb : d198467 q = 1) : d201240 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16888, d201240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16888, d201240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16889 q = 1) (hb : d198467 q = 1) : d201241 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16889, d201241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16889, d201241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53533 (p : Pattern) (ha : d16983 p = 1) (hb : d198467 p = 1) : d201348 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16973 q = 1) (hb : d198467 q = 1) : d201246 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16973, d201246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53532 q ha hb
    | true =>
      simp only [d16973, d201246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53526 q ha hb
  have h2 (q : Pattern) (ha : d16974 q = 1) (hb : d198467 q = 1) : d201247 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16974, d201247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16974, d201247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16975 q = 1) (hb : d198467 q = 1) : d201248 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16975, d201248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16975, d201248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16976 q = 1) (hb : d198467 q = 1) : d201249 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16976, d201249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16976, d201249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16977 q = 1) (hb : d198467 q = 1) : d201250 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16977, d201250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16977, d201250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16978 q = 1) (hb : d198467 q = 1) : d201343 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16978, d201343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53526 q ha hb
    | true =>
      simp only [d16978, d201343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16979 q = 1) (hb : d198467 q = 1) : d201344 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16979, d201344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16979, d201344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16980 q = 1) (hb : d198467 q = 1) : d201345 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16980, d201345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16980, d201345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16981 q = 1) (hb : d198467 q = 1) : d201346 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16981, d201346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16981, d201346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16982 q = 1) (hb : d198467 q = 1) : d201347 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16982, d201347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16982, d201347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16983 q = 1) (hb : d198467 q = 1) : d201348 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16983, d201348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16983, d201348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro53534 (p : Pattern) (ha : d16989 p = 1) (hb : d198467 p = 1) : d201354 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16978 q = 1) (hb : d198467 q = 1) : d201343 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16978, d201343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53526 q ha hb
    | true =>
      simp only [d16978, d201343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16979 q = 1) (hb : d198467 q = 1) : d201344 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16979, d201344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16979, d201344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16980 q = 1) (hb : d198467 q = 1) : d201345 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16980, d201345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16980, d201345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16981 q = 1) (hb : d198467 q = 1) : d201346 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16981, d201346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16981, d201346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16982 q = 1) (hb : d198467 q = 1) : d201347 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16982, d201347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16982, d201347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16984 q = 1) (hb : d198467 q = 1) : d201349 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16984, d201349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53529 q ha hb
    | true =>
      simp only [d16984, d201349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16985 q = 1) (hb : d198467 q = 1) : d201350 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16985, d201350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16985, d201350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16986 q = 1) (hb : d198467 q = 1) : d201351 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16986, d201351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16986, d201351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16987 q = 1) (hb : d198467 q = 1) : d201352 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16987, d201352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16987, d201352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16988 q = 1) (hb : d198467 q = 1) : d201353 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16988, d201353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16988, d201353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16989 q = 1) (hb : d198467 q = 1) : d201354 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16989, d201354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16989, d201354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro53535 (p : Pattern) (ha : d16998 p = 1) (hb : d198467 p = 1) : d201363 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16984 q = 1) (hb : d198467 q = 1) : d201349 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16984, d201349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53529 q ha hb
    | true =>
      simp only [d16984, d201349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16985 q = 1) (hb : d198467 q = 1) : d201350 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16985, d201350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16985, d201350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16986 q = 1) (hb : d198467 q = 1) : d201351 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16986, d201351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16986, d201351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16987 q = 1) (hb : d198467 q = 1) : d201352 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16987, d201352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16987, d201352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16988 q = 1) (hb : d198467 q = 1) : d201353 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16988, d201353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16988, d201353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16998 q = 1) (hb : d198467 q = 1) : d201363 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16998, d201363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16998, d201363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53536 (p : Pattern) (ha : d15435 p = 1) (hb : d198467 p = 1) : d201396 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1868 q = 1) (hb : d198467 q = 1) : d201376 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1868, d201376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1868, d201376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53513 q ha hb
  have h2 (q : Pattern) (ha : d1582 q = 1) (hb : d198467 q = 1) : d201212 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d201212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53513 q ha hb
    | true =>
      simp only [d1582, d201212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1869 q = 1) (hb : d198467 q = 1) : d201377 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1869, d201377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1869, d201377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1583 q = 1) (hb : d198467 q = 1) : d201213 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d201213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1583, d201213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1870 q = 1) (hb : d198467 q = 1) : d201378 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1870, d201378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1870, d201378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1871 q = 1) (hb : d198467 q = 1) : d201379 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1871, d201379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1871, d201379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1877 q = 1) (hb : d198467 q = 1) : d201385 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1877, d201385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1877, d201385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15416 q = 1) (hb : d198467 q = 1) : d15416 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d15435 q = 1) (hb : d198467 q = 1) : d201396 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15435, d201396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15435, d201396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro53537 (p : Pattern) (ha : d17032 p = 1) (hb : d198467 p = 1) : d201392 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1862 q = 1) (hb : d198467 q = 1) : d201371 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1862, d201371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1862, d201371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53520 q ha hb
  have h2 (q : Pattern) (ha : d1570 q = 1) (hb : d198467 q = 1) : d201206 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d201206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53520 q ha hb
    | true =>
      simp only [d1570, d201206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1863 q = 1) (hb : d198467 q = 1) : d201372 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1863, d201372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1863, d201372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1571 q = 1) (hb : d198467 q = 1) : d201207 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d201207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1571, d201207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1864 q = 1) (hb : d198467 q = 1) : d201373 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1864, d201373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1864, d201373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1865 q = 1) (hb : d198467 q = 1) : d201374 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1865, d201374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1865, d201374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17027 q = 1) (hb : d198467 q = 1) : d201376 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17027, d201376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17027, d201376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53521 q ha hb
  have h8 (q : Pattern) (ha : d10115 q = 1) (hb : d198467 q = 1) : d201212 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10115, d201212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53521 q ha hb
    | true =>
      simp only [d10115, d201212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17028 q = 1) (hb : d198467 q = 1) : d201377 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17028, d201377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17028, d201377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10117 q = 1) (hb : d198467 q = 1) : d201213 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10117, d201213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10117, d201213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d17029 q = 1) (hb : d198467 q = 1) : d201378 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17029, d201378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17029, d201378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17030 q = 1) (hb : d198467 q = 1) : d201379 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17030, d201379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17030, d201379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d17031 q = 1) (hb : d198467 q = 1) : d201391 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17031, d201391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17031, d201391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15397 q = 1) (hb : d198467 q = 1) : d201376 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15397, d201376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15397, d201376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53518 q ha hb
  have h15 (q : Pattern) (ha : d10085 q = 1) (hb : d198467 q = 1) : d201212 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d201212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53518 q ha hb
    | true =>
      simp only [d10085, d201212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d15398 q = 1) (hb : d198467 q = 1) : d201377 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15398, d201377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d15398, d201377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10087 q = 1) (hb : d198467 q = 1) : d201213 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10087, d201213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d10087, d201213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d15399 q = 1) (hb : d198467 q = 1) : d201378 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15399, d201378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d15399, d201378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d15400 q = 1) (hb : d198467 q = 1) : d201379 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15400, d201379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d15400, d201379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d15401 q = 1) (hb : d198467 q = 1) : d201385 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15401, d201385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d15401, d201385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d17032 q = 1) (hb : d198467 q = 1) : d201392 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17032, d201392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d17032, d201392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro53538 (p : Pattern) (ha : d17058 p = 1) (hb : d198467 p = 1) : d201415 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17053 q = 1) (hb : d198467 q = 1) : d201397 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17053, d201397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53537 q ha hb
    | true =>
      simp only [d17053, d201397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53536 q ha hb
  have h2 (q : Pattern) (ha : d17054 q = 1) (hb : d198467 q = 1) : d201398 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17054, d201398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17054, d201398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17055 q = 1) (hb : d198467 q = 1) : d201399 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17055, d201399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17055, d201399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17056 q = 1) (hb : d198467 q = 1) : d201405 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17056, d201405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17056, d201405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17057 q = 1) (hb : d198467 q = 1) : d201414 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17057, d201414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17057, d201414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17058 q = 1) (hb : d198467 q = 1) : d201415 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17058, d201415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17058, d201415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53539 (p : Pattern) (ha : d17130 p = 1) (hb : d198467 p = 1) : d201447 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17059 q = 1) (hb : d198467 q = 1) : d201416 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17059, d201416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53538 q ha hb
    | true =>
      simp only [d17059, d201416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17060 q = 1) (hb : d198467 q = 1) : d201417 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17060, d201417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17060, d201417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17127 q = 1) (hb : d198467 q = 1) : d201444 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17127, d201444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17127, d201444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17128 q = 1) (hb : d198467 q = 1) : d201445 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17128, d201445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17128, d201445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17129 q = 1) (hb : d198467 q = 1) : d201446 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17129, d201446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17129, d201446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17130 q = 1) (hb : d198467 q = 1) : d201447 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17130, d201447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17130, d201447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53540 (p : Pattern) (ha : d17136 p = 1) (hb : d198467 p = 1) : d201453 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17131 q = 1) (hb : d198467 q = 1) : d201448 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17131, d201448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53539 q ha hb
    | true =>
      simp only [d17131, d201448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17132 q = 1) (hb : d198467 q = 1) : d201449 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17132, d201449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17132, d201449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17133 q = 1) (hb : d198467 q = 1) : d201450 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17133, d201450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17133, d201450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17134 q = 1) (hb : d198467 q = 1) : d201451 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17134, d201451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17134, d201451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17135 q = 1) (hb : d198467 q = 1) : d201452 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17135, d201452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17135, d201452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17136 q = 1) (hb : d198467 q = 1) : d201453 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17136, d201453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17136, d201453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53541 (p : Pattern) (ha : d16843 p = 1) (hb : d198467 p = 1) : d201266 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16809 q = 1) (hb : d198467 q = 1) : d201232 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16809, d201232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53523 q ha hb
    | true =>
      simp only [d16809, d201232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16810 q = 1) (hb : d198467 q = 1) : d201233 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16810, d201233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16810, d201233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16813 q = 1) (hb : d198467 q = 1) : d201236 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d201236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53524 q ha hb
    | true =>
      simp only [d16813, d201236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16814 q = 1) (hb : d198467 q = 1) : d201237 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d201237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d201237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16815 q = 1) (hb : d198467 q = 1) : d201238 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16815, d201238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16815, d201238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16816 q = 1) (hb : d198467 q = 1) : d201239 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16816, d201239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16816, d201239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16842 q = 1) (hb : d198467 q = 1) : d201265 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16842, d201265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16842, d201265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16843 q = 1) (hb : d198467 q = 1) : d201266 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16843, d201266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16843, d201266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53542 (p : Pattern) (ha : d16845 p = 1) (hb : d198467 p = 1) : d201268 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16813 q = 1) (hb : d198467 q = 1) : d201236 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d201236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53524 q ha hb
    | true =>
      simp only [d16813, d201236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16814 q = 1) (hb : d198467 q = 1) : d201237 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d201237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d201237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16819 q = 1) (hb : d198467 q = 1) : d201242 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16819, d201242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16819, d201242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16820 q = 1) (hb : d198467 q = 1) : d201243 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16820, d201243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16820, d201243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16844 q = 1) (hb : d198467 q = 1) : d201267 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16844, d201267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16844, d201267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16845 q = 1) (hb : d198467 q = 1) : d201268 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16845, d201268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16845, d201268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53543 (p : Pattern) (ha : d16852 p = 1) (hb : d198467 p = 1) : d201275 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16809 q = 1) (hb : d198467 q = 1) : d201232 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16809, d201232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53523 q ha hb
    | true =>
      simp only [d16809, d201232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16810 q = 1) (hb : d198467 q = 1) : d201233 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16810, d201233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16810, d201233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16813 q = 1) (hb : d198467 q = 1) : d201236 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d201236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53524 q ha hb
    | true =>
      simp only [d16813, d201236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16814 q = 1) (hb : d198467 q = 1) : d201237 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d201237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d201237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16815 q = 1) (hb : d198467 q = 1) : d201238 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16815, d201238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16815, d201238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16850 q = 1) (hb : d198467 q = 1) : d201273 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16850, d201273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16850, d201273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16851 q = 1) (hb : d198467 q = 1) : d201274 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16851, d201274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16851, d201274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16852 q = 1) (hb : d198467 q = 1) : d201275 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16852, d201275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16852, d201275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53544 (p : Pattern) (ha : d16855 p = 1) (hb : d198467 p = 1) : d201278 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16813 q = 1) (hb : d198467 q = 1) : d201236 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d201236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53524 q ha hb
    | true =>
      simp only [d16813, d201236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16814 q = 1) (hb : d198467 q = 1) : d201237 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d201237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d201237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16819 q = 1) (hb : d198467 q = 1) : d201242 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16819, d201242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16819, d201242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16853 q = 1) (hb : d198467 q = 1) : d201276 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16853, d201276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16853, d201276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16854 q = 1) (hb : d198467 q = 1) : d201277 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16854, d201277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16854, d201277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16855 q = 1) (hb : d198467 q = 1) : d201278 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16855, d201278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16855, d201278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53545 (p : Pattern) (ha : d1664 p = 1) (hb : d198467 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1201 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1660 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1660, d152852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1660, d152852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1205 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1661 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1661, d152852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1661, d152852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1662 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1663 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1538 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1664 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d1664, d198467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1664, d198467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro53546 (p : Pattern) (ha : d16863 p = 1) (hb : d198467 p = 1) : d201283 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1665 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53545 q ha hb
    | true =>
      simp only [d1665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1666 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1667 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1668 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10036 q = 1) (hb : d198467 q = 1) : d201004 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10036, d201004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47297 q ha hb
    | true =>
      simp only [d10036, d201004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10038 q = 1) (hb : d198467 q = 1) : d201005 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10038, d201005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10038, d201005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16859 q = 1) (hb : d198467 q = 1) : d201006 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16859, d201006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16859, d201006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16860 q = 1) (hb : d198467 q = 1) : d201007 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16860, d201007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16860, d201007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16861 q = 1) (hb : d198467 q = 1) : d201282 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16861, d201282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16861, d201282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15230 q = 1) (hb : d198467 q = 1) : d15230 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d10063 q = 1) (hb : d198467 q = 1) : d22226 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10063, d22226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53516 q ha hb
    | true =>
      simp only [d10063, d22226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d10065 q = 1) (hb : d198467 q = 1) : d22227 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10065, d22227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10065, d22227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d15151 q = 1) (hb : d198467 q = 1) : d22228 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15151, d22228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15151, d22228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15152 q = 1) (hb : d198467 q = 1) : d22229 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15152, d22229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15152, d22229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d16862 q = 1) (hb : d198467 q = 1) : d22318 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16862, d22318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16862, d22318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16863 q = 1) (hb : d198467 q = 1) : d201283 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16863, d201283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16863, d201283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro53547 (p : Pattern) (ha : d10098 p = 1) (hb : d198467 p = 1) : d22225 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1529 q = 1) : d1529 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10056 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10095 q = 1) (hb : d152852 q = 1) : d10051 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10095, d152852, d10051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d10095, d152852, d10051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10096 q = 1) (hb : d152852 q = 1) : d10052 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10096, d10052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10096, d10052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10097 q = 1) (hb : d152852 q = 1) : d10053 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10097, d10053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10097, d10053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d10061 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d10098 q = 1) (hb : d198467 q = 1) : d22225 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d10098, d198467, d22225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10098, d198467, d22225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro53548 (p : Pattern) (ha : d16868 p = 1) (hb : d198467 p = 1) : d201287 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10099 q = 1) (hb : d198467 q = 1) : d22226 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10099, d22226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53547 q ha hb
    | true =>
      simp only [d10099, d22226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10101 q = 1) (hb : d198467 q = 1) : d22227 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10101, d22227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10101, d22227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13348 q = 1) (hb : d198467 q = 1) : d22228 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13348, d22228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13348, d22228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13349 q = 1) (hb : d198467 q = 1) : d22229 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13349, d22229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13349, d22229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10085 q = 1) (hb : d198467 q = 1) : d201212 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d201212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53518 q ha hb
    | true =>
      simp only [d10085, d201212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10087 q = 1) (hb : d198467 q = 1) : d201213 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10087, d201213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10087, d201213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15156 q = 1) (hb : d198467 q = 1) : d201214 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15156, d201214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15156, d201214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15157 q = 1) (hb : d198467 q = 1) : d201215 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15157, d201215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15157, d201215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16867 q = 1) (hb : d198467 q = 1) : d201216 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16867, d201216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16867, d201216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15158 q = 1) (hb : d198467 q = 1) : d201219 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15158, d201219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15158, d201219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16868 q = 1) (hb : d198467 q = 1) : d201287 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16868, d201287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16868, d201287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro53549 (p : Pattern) (ha : d16874 p = 1) (hb : d198467 p = 1) : d201293 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16864 q = 1) (hb : d198467 q = 1) : d201284 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16864, d201284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53546 q ha hb
    | true =>
      simp only [d16864, d201284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53519 q ha hb
  have h2 (q : Pattern) (ha : d16865 q = 1) (hb : d198467 q = 1) : d201285 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16865, d201285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16865, d201285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16866 q = 1) (hb : d198467 q = 1) : d201286 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16866, d201286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16866, d201286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16869 q = 1) (hb : d198467 q = 1) : d201288 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16869, d201288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53519 q ha hb
    | true =>
      simp only [d16869, d201288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53548 q ha hb
  have h5 (q : Pattern) (ha : d16870 q = 1) (hb : d198467 q = 1) : d201289 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16870, d201289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16870, d201289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16871 q = 1) (hb : d198467 q = 1) : d201290 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16871, d201290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16871, d201290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16872 q = 1) (hb : d198467 q = 1) : d201291 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16872, d201291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16872, d201291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16796 q = 1) (hb : d198467 q = 1) : d201221 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16796, d201221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53519 q ha hb
    | true =>
      simp only [d16796, d201221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53522 q ha hb
  have h9 (q : Pattern) (ha : d16797 q = 1) (hb : d198467 q = 1) : d201222 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16797, d201222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16797, d201222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16798 q = 1) (hb : d198467 q = 1) : d201223 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16798, d201223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16798, d201223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16799 q = 1) (hb : d198467 q = 1) : d201225 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16799, d201225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53522 q ha hb
    | true =>
      simp only [d16799, d201225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53512 q ha hb
  have h12 (q : Pattern) (ha : d16800 q = 1) (hb : d198467 q = 1) : d201226 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16800, d201226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16800, d201226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16801 q = 1) (hb : d198467 q = 1) : d201227 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16801, d201227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16801, d201227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d16802 q = 1) (hb : d198467 q = 1) : d201228 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16802, d201228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16802, d201228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16873 q = 1) (hb : d198467 q = 1) : d201292 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16873, d201292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16873, d201292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16874 q = 1) (hb : d198467 q = 1) : d201293 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16874, d201293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d16874, d201293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro53550 (p : Pattern) (ha : d16885 p = 1) (hb : d198467 p = 1) : d201299 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16875 q = 1) (hb : d198467 q = 1) : d201294 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16875, d201294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53549 q ha hb
    | true =>
      simp only [d16875, d201294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16876 q = 1) (hb : d198467 q = 1) : d201295 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16876, d201295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16876, d201295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16880 q = 1) (hb : d198467 q = 1) : d201232 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16880, d201232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53531 q ha hb
    | true =>
      simp only [d16880, d201232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16881 q = 1) (hb : d198467 q = 1) : d201233 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16881, d201233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16881, d201233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16882 q = 1) (hb : d198467 q = 1) : d201296 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16882, d201296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16882, d201296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16883 q = 1) (hb : d198467 q = 1) : d201297 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16883, d201297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16883, d201297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16884 q = 1) (hb : d198467 q = 1) : d201298 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16884, d201298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16884, d201298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16885 q = 1) (hb : d198467 q = 1) : d201299 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16885, d201299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16885, d201299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53551 (p : Pattern) (ha : d13287 p = 1) (hb : d198467 p = 1) : d201302 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1582 q = 1) (hb : d198467 q = 1) : d201212 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d201212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53513 q ha hb
    | true =>
      simp only [d1582, d201212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1583 q = 1) (hb : d198467 q = 1) : d201213 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d201213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1583, d201213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1584 q = 1) (hb : d198467 q = 1) : d201214 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1584, d201214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1584, d201214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1585 q = 1) (hb : d198467 q = 1) : d201215 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1585, d201215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1585, d201215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1588 q = 1) (hb : d198467 q = 1) : d201219 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1588, d201219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1588, d201219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13287 q = 1) (hb : d198467 q = 1) : d201302 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13287, d201302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13287, d201302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53552 (p : Pattern) (ha : d16934 p = 1) (hb : d198467 p = 1) : d201308 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16796 q = 1) (hb : d198467 q = 1) : d201221 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16796, d201221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53519 q ha hb
    | true =>
      simp only [d16796, d201221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53522 q ha hb
  have h2 (q : Pattern) (ha : d16797 q = 1) (hb : d198467 q = 1) : d201222 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16797, d201222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16797, d201222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16798 q = 1) (hb : d198467 q = 1) : d201223 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16798, d201223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16798, d201223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16799 q = 1) (hb : d198467 q = 1) : d201225 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16799, d201225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53522 q ha hb
    | true =>
      simp only [d16799, d201225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53512 q ha hb
  have h5 (q : Pattern) (ha : d16800 q = 1) (hb : d198467 q = 1) : d201226 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16800, d201226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16800, d201226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16801 q = 1) (hb : d198467 q = 1) : d201227 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16801, d201227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16801, d201227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16802 q = 1) (hb : d198467 q = 1) : d201228 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16802, d201228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16802, d201228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16929 q = 1) (hb : d198467 q = 1) : d201303 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16929, d201303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53522 q ha hb
    | true =>
      simp only [d16929, d201303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53551 q ha hb
  have h9 (q : Pattern) (ha : d16930 q = 1) (hb : d198467 q = 1) : d201304 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16930, d201304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16930, d201304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16931 q = 1) (hb : d198467 q = 1) : d201305 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16931, d201305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16931, d201305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16932 q = 1) (hb : d198467 q = 1) : d201306 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16932, d201306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16932, d201306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d16933 q = 1) (hb : d198467 q = 1) : d201307 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16933, d201307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16933, d201307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16934 q = 1) (hb : d198467 q = 1) : d201308 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16934, d201308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d16934, d201308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro53553 (p : Pattern) (ha : d16940 p = 1) (hb : d198467 p = 1) : d201314 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16935 q = 1) (hb : d198467 q = 1) : d201309 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16935, d201309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53552 q ha hb
    | true =>
      simp only [d16935, d201309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16936 q = 1) (hb : d198467 q = 1) : d201310 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16936, d201310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16936, d201310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16937 q = 1) (hb : d198467 q = 1) : d201311 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16937, d201311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16937, d201311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16938 q = 1) (hb : d198467 q = 1) : d201312 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16938, d201312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16938, d201312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16939 q = 1) (hb : d198467 q = 1) : d201313 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16939, d201313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16939, d201313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16940 q = 1) (hb : d198467 q = 1) : d201314 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16940, d201314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16940, d201314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53554 (p : Pattern) (ha : d128357 p = 1) (hb : d198467 p = 1) : d201320 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16846 q = 1) (hb : d198467 q = 1) : d201269 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16846, d201269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53541 q ha hb
    | true =>
      simp only [d16846, d201269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53542 q ha hb
  have h2 (q : Pattern) (ha : d16847 q = 1) (hb : d198467 q = 1) : d201270 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16847, d201270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16847, d201270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16848 q = 1) (hb : d198467 q = 1) : d201271 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16848, d201271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16848, d201271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16849 q = 1) (hb : d198467 q = 1) : d201272 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16849, d201272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16849, d201272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16856 q = 1) (hb : d198467 q = 1) : d201279 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16856, d201279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53543 q ha hb
    | true =>
      simp only [d16856, d201279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53544 q ha hb
  have h6 (q : Pattern) (ha : d16857 q = 1) (hb : d198467 q = 1) : d201280 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16857, d201280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16857, d201280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16858 q = 1) (hb : d198467 q = 1) : d201281 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16858, d201281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16858, d201281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16890 q = 1) (hb : d198467 q = 1) : d201300 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16890, d201300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53550 q ha hb
    | true =>
      simp only [d16890, d201300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53532 q ha hb
  have h9 (q : Pattern) (ha : d128353 q = 1) (hb : d198467 q = 1) : d201301 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128353, d201301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128353, d201301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16941 q = 1) (hb : d198467 q = 1) : d201315 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16941, d201315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53553 q ha hb
    | true =>
      simp only [d16941, d201315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16942 q = 1) (hb : d198467 q = 1) : d201316 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16942, d201316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16942, d201316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128354 q = 1) (hb : d198467 q = 1) : d201317 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128354, d201317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128354, d201317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128355 q = 1) (hb : d198467 q = 1) : d201318 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128355, d201318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128355, d201318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128356 q = 1) (hb : d198467 q = 1) : d201319 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128356, d201319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128356, d201319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128357 q = 1) (hb : d198467 q = 1) : d201320 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128357, d201320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128357, d201320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro53555 (p : Pattern) (ha : d16947 p = 1) (hb : d198467 p = 1) : d201321 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16809 q = 1) (hb : d198467 q = 1) : d201232 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16809, d201232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53523 q ha hb
    | true =>
      simp only [d16809, d201232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16810 q = 1) (hb : d198467 q = 1) : d201233 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16810, d201233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16810, d201233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16813 q = 1) (hb : d198467 q = 1) : d201236 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d201236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53524 q ha hb
    | true =>
      simp only [d16813, d201236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16814 q = 1) (hb : d198467 q = 1) : d201237 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d201237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d201237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16815 q = 1) (hb : d198467 q = 1) : d201238 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16815, d201238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16815, d201238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16816 q = 1) (hb : d198467 q = 1) : d201239 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16816, d201239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16816, d201239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16842 q = 1) (hb : d198467 q = 1) : d201265 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16842, d201265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16842, d201265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16947 q = 1) (hb : d198467 q = 1) : d201321 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16947, d201321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16947, d201321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro53556 (p : Pattern) (ha : d16948 p = 1) (hb : d198467 p = 1) : d201322 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16813 q = 1) (hb : d198467 q = 1) : d201236 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d201236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53524 q ha hb
    | true =>
      simp only [d16813, d201236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16814 q = 1) (hb : d198467 q = 1) : d201237 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d201237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d201237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16819 q = 1) (hb : d198467 q = 1) : d201242 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16819, d201242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16819, d201242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16820 q = 1) (hb : d198467 q = 1) : d201243 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16820, d201243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16820, d201243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16844 q = 1) (hb : d198467 q = 1) : d201267 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16844, d201267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16844, d201267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16948 q = 1) (hb : d198467 q = 1) : d201322 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16948, d201322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16948, d201322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53557 (p : Pattern) (ha : d16953 p = 1) (hb : d198467 p = 1) : d201327 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16809 q = 1) (hb : d198467 q = 1) : d201232 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16809, d201232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53523 q ha hb
    | true =>
      simp only [d16809, d201232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16810 q = 1) (hb : d198467 q = 1) : d201233 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16810, d201233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16810, d201233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16813 q = 1) (hb : d198467 q = 1) : d201236 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d201236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53524 q ha hb
    | true =>
      simp only [d16813, d201236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16814 q = 1) (hb : d198467 q = 1) : d201237 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d201237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d201237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16815 q = 1) (hb : d198467 q = 1) : d201238 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16815, d201238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16815, d201238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16850 q = 1) (hb : d198467 q = 1) : d201273 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16850, d201273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16850, d201273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16851 q = 1) (hb : d198467 q = 1) : d201274 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16851, d201274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16851, d201274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16953 q = 1) (hb : d198467 q = 1) : d201327 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16953, d201327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16953, d201327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro53558 (p : Pattern) (ha : d16954 p = 1) (hb : d198467 p = 1) : d201328 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16813 q = 1) (hb : d198467 q = 1) : d201236 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d201236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53524 q ha hb
    | true =>
      simp only [d16813, d201236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16814 q = 1) (hb : d198467 q = 1) : d201237 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d201237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d201237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16819 q = 1) (hb : d198467 q = 1) : d201242 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16819, d201242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16819, d201242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16853 q = 1) (hb : d198467 q = 1) : d201276 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16853, d201276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16853, d201276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16854 q = 1) (hb : d198467 q = 1) : d201277 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16854, d201277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16854, d201277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16954 q = 1) (hb : d198467 q = 1) : d201328 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16954, d201328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16954, d201328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53559 (p : Pattern) (ha : d16958 p = 1) (hb : d198467 p = 1) : d201332 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16875 q = 1) (hb : d198467 q = 1) : d201294 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16875, d201294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53549 q ha hb
    | true =>
      simp only [d16875, d201294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16876 q = 1) (hb : d198467 q = 1) : d201295 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16876, d201295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16876, d201295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16880 q = 1) (hb : d198467 q = 1) : d201232 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16880, d201232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53531 q ha hb
    | true =>
      simp only [d16880, d201232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16881 q = 1) (hb : d198467 q = 1) : d201233 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16881, d201233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16881, d201233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16882 q = 1) (hb : d198467 q = 1) : d201296 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16882, d201296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16882, d201296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16883 q = 1) (hb : d198467 q = 1) : d201297 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16883, d201297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16883, d201297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16884 q = 1) (hb : d198467 q = 1) : d201298 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16884, d201298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16884, d201298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16958 q = 1) (hb : d198467 q = 1) : d201332 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16958, d201332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16958, d201332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro53560 (p : Pattern) (ha : d16959 p = 1) (hb : d198467 p = 1) : d201254 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16880 q = 1) (hb : d198467 q = 1) : d201232 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16880, d201232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53531 q ha hb
    | true =>
      simp only [d16880, d201232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16881 q = 1) (hb : d198467 q = 1) : d201233 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16881, d201233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16881, d201233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16813 q = 1) (hb : d198467 q = 1) : d201236 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d201236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53524 q ha hb
    | true =>
      simp only [d16813, d201236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16814 q = 1) (hb : d198467 q = 1) : d201237 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d201237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d201237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16886 q = 1) (hb : d198467 q = 1) : d201238 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16886, d201238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16886, d201238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16887 q = 1) (hb : d198467 q = 1) : d201239 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16887, d201239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16887, d201239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16888 q = 1) (hb : d198467 q = 1) : d201240 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16888, d201240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16888, d201240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16959 q = 1) (hb : d198467 q = 1) : d201254 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16959, d201254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16959, d201254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro53561 (p : Pattern) (ha : d16965 p = 1) (hb : d198467 p = 1) : d201335 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16935 q = 1) (hb : d198467 q = 1) : d201309 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16935, d201309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53552 q ha hb
    | true =>
      simp only [d16935, d201309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16936 q = 1) (hb : d198467 q = 1) : d201310 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16936, d201310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16936, d201310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16937 q = 1) (hb : d198467 q = 1) : d201311 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16937, d201311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16937, d201311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16938 q = 1) (hb : d198467 q = 1) : d201312 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16938, d201312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16938, d201312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16939 q = 1) (hb : d198467 q = 1) : d201313 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16939, d201313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16939, d201313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16965 q = 1) (hb : d198467 q = 1) : d201335 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16965, d201335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16965, d201335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53562 (p : Pattern) (ha : d128362 p = 1) (hb : d198467 p = 1) : d201341 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16846 q = 1) (hb : d198467 q = 1) : d201269 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16846, d201269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53541 q ha hb
    | true =>
      simp only [d16846, d201269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53542 q ha hb
  have h2 (q : Pattern) (ha : d16847 q = 1) (hb : d198467 q = 1) : d201270 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16847, d201270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16847, d201270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16848 q = 1) (hb : d198467 q = 1) : d201271 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16848, d201271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16848, d201271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16849 q = 1) (hb : d198467 q = 1) : d201272 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16849, d201272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16849, d201272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16856 q = 1) (hb : d198467 q = 1) : d201279 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16856, d201279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53543 q ha hb
    | true =>
      simp only [d16856, d201279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53544 q ha hb
  have h6 (q : Pattern) (ha : d16857 q = 1) (hb : d198467 q = 1) : d201280 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16857, d201280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16857, d201280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16858 q = 1) (hb : d198467 q = 1) : d201281 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16858, d201281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16858, d201281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16890 q = 1) (hb : d198467 q = 1) : d201300 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16890, d201300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53550 q ha hb
    | true =>
      simp only [d16890, d201300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53532 q ha hb
  have h9 (q : Pattern) (ha : d128353 q = 1) (hb : d198467 q = 1) : d201301 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128353, d201301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128353, d201301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16941 q = 1) (hb : d198467 q = 1) : d201315 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16941, d201315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53553 q ha hb
    | true =>
      simp only [d16941, d201315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16942 q = 1) (hb : d198467 q = 1) : d201316 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16942, d201316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16942, d201316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128354 q = 1) (hb : d198467 q = 1) : d201317 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128354, d201317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128354, d201317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128355 q = 1) (hb : d198467 q = 1) : d201318 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128355, d201318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128355, d201318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128356 q = 1) (hb : d198467 q = 1) : d201319 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128356, d201319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128356, d201319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16949 q = 1) (hb : d198467 q = 1) : d201323 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16949, d201323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53555 q ha hb
    | true =>
      simp only [d16949, d201323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53556 q ha hb
  have h16 (q : Pattern) (ha : d16950 q = 1) (hb : d198467 q = 1) : d201324 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16950, d201324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16950, d201324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16951 q = 1) (hb : d198467 q = 1) : d201325 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16951, d201325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16951, d201325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d16952 q = 1) (hb : d198467 q = 1) : d201326 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16952, d201326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16952, d201326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16955 q = 1) (hb : d198467 q = 1) : d201329 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16955, d201329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53557 q ha hb
    | true =>
      simp only [d16955, d201329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53558 q ha hb
  have h20 (q : Pattern) (ha : d16956 q = 1) (hb : d198467 q = 1) : d201330 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16956, d201330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16956, d201330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d16957 q = 1) (hb : d198467 q = 1) : d201331 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16957, d201331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d16957, d201331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d16960 q = 1) (hb : d198467 q = 1) : d201333 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16960, d201333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53559 q ha hb
    | true =>
      simp only [d16960, d201333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53560 q ha hb
  have h23 (q : Pattern) (ha : d128358 q = 1) (hb : d198467 q = 1) : d201334 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128358, d201334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d128358, d201334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d16966 q = 1) (hb : d198467 q = 1) : d201336 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16966, d201336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53561 q ha hb
    | true =>
      simp only [d16966, d201336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d16967 q = 1) (hb : d198467 q = 1) : d201337 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16967, d201337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d16967, d201337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d128359 q = 1) (hb : d198467 q = 1) : d201338 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128359, d201338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d128359, d201338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d128360 q = 1) (hb : d198467 q = 1) : d201339 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128360, d201339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128360, d201339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d128361 q = 1) (hb : d198467 q = 1) : d201340 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128361, d201340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d128361, d201340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d128362 q = 1) (hb : d198467 q = 1) : d201341 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128362, d201341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128362, d201341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro53563 (p : Pattern) (ha : d128369 p = 1) (hb : d198467 p = 1) : d201361 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16960 q = 1) (hb : d198467 q = 1) : d201333 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16960, d201333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53559 q ha hb
    | true =>
      simp only [d16960, d201333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53560 q ha hb
  have h2 (q : Pattern) (ha : d128358 q = 1) (hb : d198467 q = 1) : d201334 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128358, d201334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128358, d201334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16966 q = 1) (hb : d198467 q = 1) : d201336 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16966, d201336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53561 q ha hb
    | true =>
      simp only [d16966, d201336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16967 q = 1) (hb : d198467 q = 1) : d201337 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16967, d201337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16967, d201337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128359 q = 1) (hb : d198467 q = 1) : d201338 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128359, d201338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128359, d201338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128367 q = 1) (hb : d198467 q = 1) : d201359 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128367, d201359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128367, d201359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128368 q = 1) (hb : d198467 q = 1) : d201360 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128368, d201360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128368, d201360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128369 q = 1) (hb : d198467 q = 1) : d201361 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128369, d201361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128369, d201361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53564 (p : Pattern) (ha : d15417 p = 1) (hb : d198467 p = 1) : d201396 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6496 q = 1) (hb : d198467 q = 1) : d201376 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d6496, d201376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6496, d201376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53511 q ha hb
  have h2 (q : Pattern) (ha : d5134 q = 1) (hb : d198467 q = 1) : d201212 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5134, d201212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53511 q ha hb
    | true =>
      simp only [d5134, d201212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6497 q = 1) (hb : d198467 q = 1) : d201377 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d6497, d201377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6497, d201377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5135 q = 1) (hb : d198467 q = 1) : d201213 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5135, d201213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5135, d201213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6498 q = 1) (hb : d198467 q = 1) : d201378 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d6498, d201378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6498, d201378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6499 q = 1) (hb : d198467 q = 1) : d201379 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d6499, d201379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6499, d201379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6500 q = 1) (hb : d198467 q = 1) : d201385 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d6500, d201385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6500, d201385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15416 q = 1) (hb : d198467 q = 1) : d15416 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d15417 q = 1) (hb : d198467 q = 1) : d201396 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15417, d201396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15417, d201396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro53565 (p : Pattern) (ha : d17010 p = 1) (hb : d198467 p = 1) : d201370 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1853 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53545 q ha hb
  have h2 (q : Pattern) (ha : d1665 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53545 q ha hb
    | true =>
      simp only [d1665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1854 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1666 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1855 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1856 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17004 q = 1) (hb : d198467 q = 1) : d201096 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17004, d201096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17004, d201096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47297 q ha hb
  have h8 (q : Pattern) (ha : d10036 q = 1) (hb : d198467 q = 1) : d201004 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10036, d201004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47297 q ha hb
    | true =>
      simp only [d10036, d201004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17005 q = 1) (hb : d198467 q = 1) : d201097 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17005, d201097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17005, d201097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10038 q = 1) (hb : d198467 q = 1) : d201005 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10038, d201005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10038, d201005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d17006 q = 1) (hb : d198467 q = 1) : d201098 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17006, d201098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17006, d201098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17007 q = 1) (hb : d198467 q = 1) : d201099 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17007, d201099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17007, d201099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d17008 q = 1) (hb : d198467 q = 1) : d201369 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17008, d201369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17008, d201369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15383 q = 1) (hb : d198467 q = 1) : d15383 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d15387 q = 1) (hb : d198467 q = 1) : d22502 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15387, d22502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15387, d22502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53516 q ha hb
  have h16 (q : Pattern) (ha : d10063 q = 1) (hb : d198467 q = 1) : d22226 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10063, d22226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53516 q ha hb
    | true =>
      simp only [d10063, d22226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d15388 q = 1) (hb : d198467 q = 1) : d22503 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15388, d22503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d15388, d22503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d10065 q = 1) (hb : d198467 q = 1) : d22227 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10065, d22227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10065, d22227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d15389 q = 1) (hb : d198467 q = 1) : d22504 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15389, d22504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d15389, d22504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d15390 q = 1) (hb : d198467 q = 1) : d22505 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15390, d22505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d15390, d22505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d17009 q = 1) (hb : d198467 q = 1) : d22506 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17009, d22506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d17009, d22506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d17010 q = 1) (hb : d198467 q = 1) : d201370 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17010, d201370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d17010, d201370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro53566 (p : Pattern) (ha : d17017 p = 1) (hb : d198467 p = 1) : d201381 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1857 q = 1) (hb : d198467 q = 1) : d201096 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1857, d201096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1857, d201096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53515 q ha hb
  have h2 (q : Pattern) (ha : d1555 q = 1) (hb : d198467 q = 1) : d201004 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1555, d201004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53515 q ha hb
    | true =>
      simp only [d1555, d201004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1858 q = 1) (hb : d198467 q = 1) : d201097 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1858, d201097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1858, d201097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1556 q = 1) (hb : d198467 q = 1) : d201005 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1556, d201005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1556, d201005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1859 q = 1) (hb : d198467 q = 1) : d201098 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1859, d201098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1859, d201098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1860 q = 1) (hb : d198467 q = 1) : d201099 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1860, d201099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1860, d201099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17011 q = 1) (hb : d198467 q = 1) : d201371 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17011, d201371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17011, d201371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53517 q ha hb
  have h8 (q : Pattern) (ha : d10074 q = 1) (hb : d198467 q = 1) : d201206 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10074, d201206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53517 q ha hb
    | true =>
      simp only [d10074, d201206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17012 q = 1) (hb : d198467 q = 1) : d201372 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17012, d201372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17012, d201372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10076 q = 1) (hb : d198467 q = 1) : d201207 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10076, d201207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10076, d201207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d17013 q = 1) (hb : d198467 q = 1) : d201373 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17013, d201373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17013, d201373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17014 q = 1) (hb : d198467 q = 1) : d201374 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17014, d201374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17014, d201374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d17015 q = 1) (hb : d198467 q = 1) : d201375 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17015, d201375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17015, d201375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15387 q = 1) (hb : d198467 q = 1) : d22502 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15387, d22502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15387, d22502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53516 q ha hb
  have h15 (q : Pattern) (ha : d10063 q = 1) (hb : d198467 q = 1) : d22226 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10063, d22226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53516 q ha hb
    | true =>
      simp only [d10063, d22226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d15388 q = 1) (hb : d198467 q = 1) : d22503 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15388, d22503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d15388, d22503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10065 q = 1) (hb : d198467 q = 1) : d22227 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10065, d22227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d10065, d22227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d15389 q = 1) (hb : d198467 q = 1) : d22504 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15389, d22504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d15389, d22504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d15390 q = 1) (hb : d198467 q = 1) : d22505 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15390, d22505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d15390, d22505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d15397 q = 1) (hb : d198467 q = 1) : d201376 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15397, d201376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15397, d201376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53518 q ha hb
  have h21 (q : Pattern) (ha : d10085 q = 1) (hb : d198467 q = 1) : d201212 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d201212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53518 q ha hb
    | true =>
      simp only [d10085, d201212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d15398 q = 1) (hb : d198467 q = 1) : d201377 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15398, d201377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d15398, d201377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d10087 q = 1) (hb : d198467 q = 1) : d201213 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10087, d201213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d10087, d201213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d15399 q = 1) (hb : d198467 q = 1) : d201378 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15399, d201378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d15399, d201378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d15400 q = 1) (hb : d198467 q = 1) : d201379 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15400, d201379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d15400, d201379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d17016 q = 1) (hb : d198467 q = 1) : d201380 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17016, d201380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d17016, d201380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d17017 q = 1) (hb : d198467 q = 1) : d201381 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17017, d201381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d17017, d201381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro53567 (p : Pattern) (ha : d17022 p = 1) (hb : d198467 p = 1) : d201386 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13486 q = 1) (hb : d198467 q = 1) : d22502 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13486, d22502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13486, d22502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53547 q ha hb
  have h2 (q : Pattern) (ha : d10099 q = 1) (hb : d198467 q = 1) : d22226 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10099, d22226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53547 q ha hb
    | true =>
      simp only [d10099, d22226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13487 q = 1) (hb : d198467 q = 1) : d22503 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13487, d22503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13487, d22503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10101 q = 1) (hb : d198467 q = 1) : d22227 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10101, d22227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10101, d22227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13488 q = 1) (hb : d198467 q = 1) : d22504 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13488, d22504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13488, d22504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13489 q = 1) (hb : d198467 q = 1) : d22505 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13489, d22505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13489, d22505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15397 q = 1) (hb : d198467 q = 1) : d201376 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15397, d201376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15397, d201376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53518 q ha hb
  have h8 (q : Pattern) (ha : d10085 q = 1) (hb : d198467 q = 1) : d201212 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d201212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53518 q ha hb
    | true =>
      simp only [d10085, d201212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15398 q = 1) (hb : d198467 q = 1) : d201377 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15398, d201377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15398, d201377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10087 q = 1) (hb : d198467 q = 1) : d201213 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10087, d201213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10087, d201213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d15399 q = 1) (hb : d198467 q = 1) : d201378 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15399, d201378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15399, d201378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d15400 q = 1) (hb : d198467 q = 1) : d201379 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15400, d201379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15400, d201379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d17021 q = 1) (hb : d198467 q = 1) : d201380 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17021, d201380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17021, d201380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15401 q = 1) (hb : d198467 q = 1) : d201385 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15401, d201385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15401, d201385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d17022 q = 1) (hb : d198467 q = 1) : d201386 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17022, d201386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d17022, d201386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro53568 (p : Pattern) (ha : d17041 p = 1) (hb : d198467 p = 1) : d201402 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17018 q = 1) (hb : d198467 q = 1) : d201382 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17018, d201382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53565 q ha hb
    | true =>
      simp only [d17018, d201382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53566 q ha hb
  have h2 (q : Pattern) (ha : d17019 q = 1) (hb : d198467 q = 1) : d201383 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17019, d201383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17019, d201383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17020 q = 1) (hb : d198467 q = 1) : d201384 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17020, d201384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17020, d201384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17023 q = 1) (hb : d198467 q = 1) : d201387 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17023, d201387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53566 q ha hb
    | true =>
      simp only [d17023, d201387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53567 q ha hb
  have h5 (q : Pattern) (ha : d17024 q = 1) (hb : d198467 q = 1) : d201388 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17024, d201388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17024, d201388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17025 q = 1) (hb : d198467 q = 1) : d201389 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17025, d201389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17025, d201389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17026 q = 1) (hb : d198467 q = 1) : d201390 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17026, d201390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17026, d201390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17033 q = 1) (hb : d198467 q = 1) : d201393 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17033, d201393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53566 q ha hb
    | true =>
      simp only [d17033, d201393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53537 q ha hb
  have h9 (q : Pattern) (ha : d17034 q = 1) (hb : d198467 q = 1) : d201394 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17034, d201394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17034, d201394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17035 q = 1) (hb : d198467 q = 1) : d201395 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17035, d201395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17035, d201395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17036 q = 1) (hb : d198467 q = 1) : d201397 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17036, d201397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53537 q ha hb
    | true =>
      simp only [d17036, d201397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53564 q ha hb
  have h12 (q : Pattern) (ha : d17037 q = 1) (hb : d198467 q = 1) : d201398 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17037, d201398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17037, d201398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17038 q = 1) (hb : d198467 q = 1) : d201399 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17038, d201399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17038, d201399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d17039 q = 1) (hb : d198467 q = 1) : d201400 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17039, d201400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17039, d201400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17040 q = 1) (hb : d198467 q = 1) : d201401 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17040, d201401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17040, d201401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d17041 q = 1) (hb : d198467 q = 1) : d201402 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17041, d201402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d17041, d201402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro53569 (p : Pattern) (ha : d17046 p = 1) (hb : d198467 p = 1) : d201407 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17033 q = 1) (hb : d198467 q = 1) : d201393 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17033, d201393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53566 q ha hb
    | true =>
      simp only [d17033, d201393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53537 q ha hb
  have h2 (q : Pattern) (ha : d17034 q = 1) (hb : d198467 q = 1) : d201394 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17034, d201394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17034, d201394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17035 q = 1) (hb : d198467 q = 1) : d201395 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17035, d201395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17035, d201395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17036 q = 1) (hb : d198467 q = 1) : d201397 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17036, d201397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53537 q ha hb
    | true =>
      simp only [d17036, d201397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53564 q ha hb
  have h5 (q : Pattern) (ha : d17037 q = 1) (hb : d198467 q = 1) : d201398 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17037, d201398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17037, d201398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17038 q = 1) (hb : d198467 q = 1) : d201399 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17038, d201399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17038, d201399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17039 q = 1) (hb : d198467 q = 1) : d201400 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17039, d201400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17039, d201400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17044 q = 1) (hb : d198467 q = 1) : d201405 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17044, d201405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17044, d201405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17045 q = 1) (hb : d198467 q = 1) : d201406 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17045, d201406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17045, d201406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17046 q = 1) (hb : d198467 q = 1) : d201407 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17046, d201407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17046, d201407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro53570 (p : Pattern) (ha : d17052 p = 1) (hb : d198467 p = 1) : d201413 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17042 q = 1) (hb : d198467 q = 1) : d201403 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17042, d201403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53568 q ha hb
    | true =>
      simp only [d17042, d201403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17043 q = 1) (hb : d198467 q = 1) : d201404 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17043, d201404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17043, d201404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17047 q = 1) (hb : d198467 q = 1) : d201408 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17047, d201408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53569 q ha hb
    | true =>
      simp only [d17047, d201408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17048 q = 1) (hb : d198467 q = 1) : d201409 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17048, d201409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17048, d201409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17049 q = 1) (hb : d198467 q = 1) : d201410 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17049, d201410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17049, d201410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17050 q = 1) (hb : d198467 q = 1) : d201411 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17050, d201411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17050, d201411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17051 q = 1) (hb : d198467 q = 1) : d201412 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17051, d201412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17051, d201412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17052 q = 1) (hb : d198467 q = 1) : d201413 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17052, d201413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17052, d201413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro53571 (p : Pattern) (ha : d17064 p = 1) (hb : d198467 p = 1) : d201421 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17047 q = 1) (hb : d198467 q = 1) : d201408 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17047, d201408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53569 q ha hb
    | true =>
      simp only [d17047, d201408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17048 q = 1) (hb : d198467 q = 1) : d201409 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17048, d201409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17048, d201409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17059 q = 1) (hb : d198467 q = 1) : d201416 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17059, d201416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53538 q ha hb
    | true =>
      simp only [d17059, d201416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17060 q = 1) (hb : d198467 q = 1) : d201417 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17060, d201417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17060, d201417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17061 q = 1) (hb : d198467 q = 1) : d201418 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17061, d201418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17061, d201418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17062 q = 1) (hb : d198467 q = 1) : d201419 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17062, d201419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17062, d201419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17063 q = 1) (hb : d198467 q = 1) : d201420 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17063, d201420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17063, d201420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17064 q = 1) (hb : d198467 q = 1) : d201421 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17064, d201421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17064, d201421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro53572 (p : Pattern) (ha : d13516 p = 1) (hb : d198467 p = 1) : d201424 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1868 q = 1) (hb : d198467 q = 1) : d201376 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1868, d201376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1868, d201376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53513 q ha hb
  have h2 (q : Pattern) (ha : d1582 q = 1) (hb : d198467 q = 1) : d201212 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d201212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53513 q ha hb
    | true =>
      simp only [d1582, d201212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1869 q = 1) (hb : d198467 q = 1) : d201377 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1869, d201377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1869, d201377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1583 q = 1) (hb : d198467 q = 1) : d201213 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d201213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1583, d201213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1870 q = 1) (hb : d198467 q = 1) : d201378 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1870, d201378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1870, d201378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1871 q = 1) (hb : d198467 q = 1) : d201379 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1871, d201379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1871, d201379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1877 q = 1) (hb : d198467 q = 1) : d201385 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1877, d201385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1877, d201385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13516 q = 1) (hb : d198467 q = 1) : d201424 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13516, d201424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13516, d201424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro53573 (p : Pattern) (ha : d17113 p = 1) (hb : d198467 p = 1) : d201430 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17033 q = 1) (hb : d198467 q = 1) : d201393 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17033, d201393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53566 q ha hb
    | true =>
      simp only [d17033, d201393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53537 q ha hb
  have h2 (q : Pattern) (ha : d17034 q = 1) (hb : d198467 q = 1) : d201394 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17034, d201394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17034, d201394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17035 q = 1) (hb : d198467 q = 1) : d201395 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17035, d201395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17035, d201395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17036 q = 1) (hb : d198467 q = 1) : d201397 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17036, d201397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53537 q ha hb
    | true =>
      simp only [d17036, d201397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53564 q ha hb
  have h5 (q : Pattern) (ha : d17037 q = 1) (hb : d198467 q = 1) : d201398 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17037, d201398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17037, d201398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17038 q = 1) (hb : d198467 q = 1) : d201399 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17038, d201399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17038, d201399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17039 q = 1) (hb : d198467 q = 1) : d201400 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17039, d201400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17039, d201400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17108 q = 1) (hb : d198467 q = 1) : d201425 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17108, d201425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53537 q ha hb
    | true =>
      simp only [d17108, d201425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53572 q ha hb
  have h9 (q : Pattern) (ha : d17109 q = 1) (hb : d198467 q = 1) : d201426 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17109, d201426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17109, d201426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17110 q = 1) (hb : d198467 q = 1) : d201427 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17110, d201427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17110, d201427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17111 q = 1) (hb : d198467 q = 1) : d201428 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17111, d201428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17111, d201428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d17112 q = 1) (hb : d198467 q = 1) : d201429 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17112, d201429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17112, d201429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17113 q = 1) (hb : d198467 q = 1) : d201430 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17113, d201430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17113, d201430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro53574 (p : Pattern) (ha : d17119 p = 1) (hb : d198467 p = 1) : d201436 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17114 q = 1) (hb : d198467 q = 1) : d201431 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17114, d201431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53573 q ha hb
    | true =>
      simp only [d17114, d201431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17115 q = 1) (hb : d198467 q = 1) : d201432 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17115, d201432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17115, d201432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17116 q = 1) (hb : d198467 q = 1) : d201433 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17116, d201433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17116, d201433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17117 q = 1) (hb : d198467 q = 1) : d201434 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17117, d201434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17117, d201434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17118 q = 1) (hb : d198467 q = 1) : d201435 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17118, d201435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17118, d201435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17119 q = 1) (hb : d198467 q = 1) : d201436 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17119, d201436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17119, d201436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53575 (p : Pattern) (ha : d128379 p = 1) (hb : d198467 p = 1) : d201442 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17065 q = 1) (hb : d198467 q = 1) : d201422 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17065, d201422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53570 q ha hb
    | true =>
      simp only [d17065, d201422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53571 q ha hb
  have h2 (q : Pattern) (ha : d128375 q = 1) (hb : d198467 q = 1) : d201423 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128375, d201423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128375, d201423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17120 q = 1) (hb : d198467 q = 1) : d201437 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17120, d201437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53574 q ha hb
    | true =>
      simp only [d17120, d201437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17121 q = 1) (hb : d198467 q = 1) : d201438 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17121, d201438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17121, d201438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128376 q = 1) (hb : d198467 q = 1) : d201439 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128376, d201439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128376, d201439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128377 q = 1) (hb : d198467 q = 1) : d201440 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128377, d201440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128377, d201440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128378 q = 1) (hb : d198467 q = 1) : d201441 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128378, d201441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128378, d201441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128379 q = 1) (hb : d198467 q = 1) : d201442 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128379, d201442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128379, d201442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53576 (p : Pattern) (ha : d128385 p = 1) (hb : d198467 p = 1) : d201459 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16829 q = 1) (hb : d198467 q = 1) : d201252 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16829, d201252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16829, d201252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53527 q ha hb
  have h2 (q : Pattern) (ha : d16830 q = 1) (hb : d198467 q = 1) : d201253 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16830, d201253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16830, d201253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16839 q = 1) (hb : d198467 q = 1) : d201262 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16839, d201262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53527 q ha hb
    | true =>
      simp only [d16839, d201262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53530 q ha hb
  have h4 (q : Pattern) (ha : d16840 q = 1) (hb : d198467 q = 1) : d201263 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16840, d201263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16840, d201263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16841 q = 1) (hb : d198467 q = 1) : d201264 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d16841, d201264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16841, d201264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128363 q = 1) (hb : d198467 q = 1) : d201342 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128363, d201342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53554 q ha hb
    | true =>
      simp only [d128363, d201342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53562 q ha hb
  have h7 (q : Pattern) (ha : d16990 q = 1) (hb : d198467 q = 1) : d201355 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16990, d201355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53533 q ha hb
    | true =>
      simp only [d16990, d201355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53534 q ha hb
  have h8 (q : Pattern) (ha : d128364 q = 1) (hb : d198467 q = 1) : d201356 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128364, d201356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128364, d201356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128365 q = 1) (hb : d198467 q = 1) : d201357 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128365, d201357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128365, d201357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d128366 q = 1) (hb : d198467 q = 1) : d201358 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128366, d201358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128366, d201358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128370 q = 1) (hb : d198467 q = 1) : d201362 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128370, d201362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128370, d201362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53563 q ha hb
  have h12 (q : Pattern) (ha : d16999 q = 1) (hb : d198467 q = 1) : d201364 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16999, d201364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16999, d201364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53535 q ha hb
  have h13 (q : Pattern) (ha : d128371 q = 1) (hb : d198467 q = 1) : d201365 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128371, d201365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128371, d201365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128372 q = 1) (hb : d198467 q = 1) : d201366 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128372, d201366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128372, d201366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d128373 q = 1) (hb : d198467 q = 1) : d201367 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128373, d201367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128373, d201367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d128374 q = 1) (hb : d198467 q = 1) : d201368 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128374, d201368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128374, d201368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d128380 q = 1) (hb : d198467 q = 1) : d201443 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128380, d201443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128380, d201443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53575 q ha hb
  have h18 (q : Pattern) (ha : d17137 q = 1) (hb : d198467 q = 1) : d201454 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17137, d201454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17137, d201454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53540 q ha hb
  have h19 (q : Pattern) (ha : d128381 q = 1) (hb : d198467 q = 1) : d201455 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128381, d201455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128381, d201455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d128382 q = 1) (hb : d198467 q = 1) : d201456 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128382, d201456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d128382, d201456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d128383 q = 1) (hb : d198467 q = 1) : d201457 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128383, d201457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d128383, d201457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d128384 q = 1) (hb : d198467 q = 1) : d201458 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128384, d201458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128384, d201458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d128385 q = 1) (hb : d198467 q = 1) : d201459 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128385, d201459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128385, d201459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro53577 (p : Pattern) (ha : d128391 p = 1) (hb : d198467 p = 1) : d201465 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128386 q = 1) (hb : d198467 q = 1) : d201460 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128386, d201460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128386, d201460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53576 q ha hb
  have h2 (q : Pattern) (ha : d128387 q = 1) (hb : d198467 q = 1) : d201461 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128387, d201461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128387, d201461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128388 q = 1) (hb : d198467 q = 1) : d201462 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128388, d201462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128388, d201462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128389 q = 1) (hb : d198467 q = 1) : d201463 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128389, d201463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128389, d201463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128390 q = 1) (hb : d198467 q = 1) : d201464 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128390, d201464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128390, d201464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128391 q = 1) (hb : d198467 q = 1) : d201465 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128391, d201465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128391, d201465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53578 (p : Pattern) (ha : d5246 p = 1) (hb : d198467 p = 1) : d201471 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2025 q = 1) : d2025 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5239 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5240 q = 1) (hb : d152852 q = 1) : d5715 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5240, d152852, d5715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5240, d152852, d5715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d2030 q = 1) : d2030 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d2048 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2049 q = 1) (hb : d152852 q = 1) : d27032 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2049, d152852, d27032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d2049, d152852, d27032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d5241 q = 1) (hb : d152852 q = 1) : d27033 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5241, d27033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5241, d27033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d5242 q = 1) (hb : d152852 q = 1) : d27034 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5242, d27034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5242, d27034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d5245 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d5246 q = 1) (hb : d198467 q = 1) : d201471 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d5246, d198467, d201471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5246, d198467, d201471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro53579 (p : Pattern) (ha : d15558 p = 1) (hb : d198467 p = 1) : d201482 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5247 q = 1) (hb : d198467 q = 1) : d201472 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5247, d201472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53578 q ha hb
    | true =>
      simp only [d5247, d201472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5248 q = 1) (hb : d198467 q = 1) : d201473 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5248, d201473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5248, d201473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5249 q = 1) (hb : d198467 q = 1) : d201474 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5249, d201474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5249, d201474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5250 q = 1) (hb : d198467 q = 1) : d201475 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5250, d201475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5250, d201475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5251 q = 1) (hb : d198467 q = 1) : d201481 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5251, d201481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5251, d201481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15557 q = 1) (hb : d198467 q = 1) : d15557 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15558 q = 1) (hb : d198467 q = 1) : d201482 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15558, d201482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15558, d201482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro53580 (p : Pattern) (ha : d2064 p = 1) (hb : d198467 p = 1) : d201471 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2025 q = 1) : d2025 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2044 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2045 q = 1) (hb : d152852 q = 1) : d5715 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2045, d152852, d5715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2045, d152852, d5715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d2030 q = 1) : d2030 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d2048 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2049 q = 1) (hb : d152852 q = 1) : d27032 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2049, d152852, d27032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d2049, d152852, d27032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d2050 q = 1) (hb : d152852 q = 1) : d27033 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d2050, d27033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2050, d27033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2051 q = 1) (hb : d152852 q = 1) : d27034 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d2051, d27034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2051, d27034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d2063 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d2064 q = 1) (hb : d198467 q = 1) : d201471 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d2064, d198467, d201471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2064, d198467, d201471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro53581 (p : Pattern) (ha : d15563 p = 1) (hb : d198467 p = 1) : d201482 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2065 q = 1) (hb : d198467 q = 1) : d201472 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d201472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53580 q ha hb
    | true =>
      simp only [d2065, d201472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2066 q = 1) (hb : d198467 q = 1) : d201473 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, d201473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2066, d201473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2067 q = 1) (hb : d198467 q = 1) : d201474 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2067, d201474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2067, d201474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2068 q = 1) (hb : d198467 q = 1) : d201475 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2068, d201475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2068, d201475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2071 q = 1) (hb : d198467 q = 1) : d201481 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2071, d201481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2071, d201481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15557 q = 1) (hb : d198467 q = 1) : d15557 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15563 q = 1) (hb : d198467 q = 1) : d201482 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15563, d201482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15563, d201482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro53582 (p : Pattern) (ha : d2034 p = 1) (hb : d198467 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2009 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2010 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2010, d152852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2010, d152852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2011 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d2011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2012 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d2012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d2033 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2034 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d2034, d198467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2034, d198467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro53583 (p : Pattern) (ha : d10370 p = 1) (hb : d198467 p = 1) : d13677 p = 1 := by
  have h0 (q : Pattern) (ha : d5717 q = 1) (hb : d152852 q = 1) : d5717 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5245 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10370 q = 1) (hb : d198467 q = 1) : d13677 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d10370, d198467, d13677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10370, d198467, d13677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro53584 (p : Pattern) (ha : d17157 p = 1) (hb : d198467 p = 1) : d201470 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2035 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53582 q ha hb
    | true =>
      simp only [d2035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2036 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2037 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2038 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10364 q = 1) (hb : d198467 q = 1) : d10353 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10364, d10353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47362 q ha hb
    | true =>
      simp only [d10364, d10353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10366 q = 1) (hb : d198467 q = 1) : d10355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10366, d10355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10366, d10355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17153 q = 1) (hb : d198467 q = 1) : d13675 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17153, d13675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17153, d13675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17154 q = 1) (hb : d198467 q = 1) : d13676 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17154, d13676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17154, d13676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17155 q = 1) (hb : d198467 q = 1) : d17228 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17155, d17228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17155, d17228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13676 q = 1) (hb : d198467 q = 1) : d13676 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d10371 q = 1) (hb : d198467 q = 1) : d13678 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, d13678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53583 q ha hb
    | true =>
      simp only [d10371, d13678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d10373 q = 1) (hb : d198467 q = 1) : d13679 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10373, d13679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10373, d13679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d15548 q = 1) (hb : d198467 q = 1) : d13680 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15548, d13680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15548, d13680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15549 q = 1) (hb : d198467 q = 1) : d13681 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15549, d13681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15549, d13681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d17156 q = 1) (hb : d198467 q = 1) : d13682 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17156, d13682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17156, d13682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d17157 q = 1) (hb : d198467 q = 1) : d201470 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17157, d201470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17157, d201470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro53585 (p : Pattern) (ha : d2052 p = 1) (hb : d198467 p = 1) : d10352 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2009 q = 1) : d2009 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2025 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2026 q = 1) (hb : d152852 q = 1) : d10349 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2026, d152852, d10349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2026, d152852, d10349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d2030 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2031 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2031, d152852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2031, d152852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d2032 q = 1) (hb : d152852 q = 1) : d10350 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d2032, d10350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2032, d10350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2033 q = 1) (hb : d152852 q = 1) : d10351 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d2033, d10351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2033, d10351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d2051 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d2052 q = 1) (hb : d198467 q = 1) : d10352 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d2052, d198467, d10352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2052, d198467, d10352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro53586 (p : Pattern) (ha : d10390 p = 1) (hb : d198467 p = 1) : d201471 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2025 q = 1) : d2025 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2044 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2045 q = 1) (hb : d152852 q = 1) : d5715 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2045, d152852, d5715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2045, d152852, d5715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d2030 q = 1) : d2030 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d2048 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2049 q = 1) (hb : d152852 q = 1) : d27032 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2049, d152852, d27032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d2049, d152852, d27032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d2050 q = 1) (hb : d152852 q = 1) : d27033 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d2050, d27033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2050, d27033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2051 q = 1) (hb : d152852 q = 1) : d27034 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d2051, d27034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2051, d27034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d5245 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d10390 q = 1) (hb : d198467 q = 1) : d201471 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d10390, d198467, d201471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10390, d198467, d201471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro53587 (p : Pattern) (ha : d17161 p = 1) (hb : d198467 p = 1) : d201477 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2053 q = 1) (hb : d198467 q = 1) : d10353 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2053, d10353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53585 q ha hb
    | true =>
      simp only [d2053, d10353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2054 q = 1) (hb : d198467 q = 1) : d10355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2054, d10355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2054, d10355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2055 q = 1) (hb : d198467 q = 1) : d13675 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2055, d13675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2055, d13675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2056 q = 1) (hb : d198467 q = 1) : d13676 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2056, d13676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2056, d13676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10391 q = 1) (hb : d198467 q = 1) : d201472 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10391, d201472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53586 q ha hb
    | true =>
      simp only [d10391, d201472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10393 q = 1) (hb : d198467 q = 1) : d201473 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10393, d201473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10393, d201473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17158 q = 1) (hb : d198467 q = 1) : d201474 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17158, d201474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17158, d201474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17159 q = 1) (hb : d198467 q = 1) : d201475 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17159, d201475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17159, d201475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17160 q = 1) (hb : d198467 q = 1) : d201476 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17160, d201476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17160, d201476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10371 q = 1) (hb : d198467 q = 1) : d13678 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, d13678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53583 q ha hb
    | true =>
      simp only [d10371, d13678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d10373 q = 1) (hb : d198467 q = 1) : d13679 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10373, d13679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10373, d13679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15548 q = 1) (hb : d198467 q = 1) : d13680 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15548, d13680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15548, d13680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15549 q = 1) (hb : d198467 q = 1) : d13681 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15549, d13681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15549, d13681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d15550 q = 1) (hb : d198467 q = 1) : d22693 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15550, d22693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15550, d22693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d17161 q = 1) (hb : d198467 q = 1) : d201477 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17161, d201477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17161, d201477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro53588 (p : Pattern) (ha : d17174 p = 1) (hb : d198467 p = 1) : d201489 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17162 q = 1) (hb : d198467 q = 1) : d201478 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17162, d201478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53584 q ha hb
    | true =>
      simp only [d17162, d201478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53587 q ha hb
  have h2 (q : Pattern) (ha : d17163 q = 1) (hb : d198467 q = 1) : d201479 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17163, d201479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17163, d201479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17164 q = 1) (hb : d198467 q = 1) : d201480 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17164, d201480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17164, d201480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17165 q = 1) (hb : d198467 q = 1) : d201483 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17165, d201483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53587 q ha hb
    | true =>
      simp only [d17165, d201483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53579 q ha hb
  have h5 (q : Pattern) (ha : d17166 q = 1) (hb : d198467 q = 1) : d201484 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17166, d201484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17166, d201484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17167 q = 1) (hb : d198467 q = 1) : d201485 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17167, d201485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17167, d201485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17168 q = 1) (hb : d198467 q = 1) : d201486 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17168, d201486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17168, d201486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17169 q = 1) (hb : d198467 q = 1) : d201483 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17169, d201483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53587 q ha hb
    | true =>
      simp only [d17169, d201483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53581 q ha hb
  have h9 (q : Pattern) (ha : d17170 q = 1) (hb : d198467 q = 1) : d201484 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17170, d201484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17170, d201484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17171 q = 1) (hb : d198467 q = 1) : d201485 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17171, d201485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17171, d201485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17172 q = 1) (hb : d198467 q = 1) : d201487 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17172, d201487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17172, d201487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d17173 q = 1) (hb : d198467 q = 1) : d201488 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17173, d201488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17173, d201488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17174 q = 1) (hb : d198467 q = 1) : d201489 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17174, d201489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17174, d201489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro53589 (p : Pattern) (ha : d17178 p = 1) (hb : d198467 p = 1) : d201493 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17169 q = 1) (hb : d198467 q = 1) : d201483 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17169, d201483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53587 q ha hb
    | true =>
      simp only [d17169, d201483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53581 q ha hb
  have h2 (q : Pattern) (ha : d17170 q = 1) (hb : d198467 q = 1) : d201484 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17170, d201484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17170, d201484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17171 q = 1) (hb : d198467 q = 1) : d201485 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17171, d201485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17171, d201485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17172 q = 1) (hb : d198467 q = 1) : d201487 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17172, d201487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17172, d201487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17177 q = 1) (hb : d198467 q = 1) : d201492 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17177, d201492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17177, d201492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17178 q = 1) (hb : d198467 q = 1) : d201493 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17178, d201493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17178, d201493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53590 (p : Pattern) (ha : d17184 p = 1) (hb : d198467 p = 1) : d201499 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17175 q = 1) (hb : d198467 q = 1) : d201490 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17175, d201490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53588 q ha hb
    | true =>
      simp only [d17175, d201490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17176 q = 1) (hb : d198467 q = 1) : d201491 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17176, d201491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17176, d201491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17179 q = 1) (hb : d198467 q = 1) : d201494 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d201494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53589 q ha hb
    | true =>
      simp only [d17179, d201494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17180 q = 1) (hb : d198467 q = 1) : d201495 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d201495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d201495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17181 q = 1) (hb : d198467 q = 1) : d201496 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17181, d201496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17181, d201496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17182 q = 1) (hb : d198467 q = 1) : d201497 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17182, d201497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17182, d201497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17183 q = 1) (hb : d198467 q = 1) : d201498 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17183, d201498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17183, d201498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17184 q = 1) (hb : d198467 q = 1) : d201499 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17184, d201499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17184, d201499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53591 (p : Pattern) (ha : d17188 p = 1) (hb : d198467 p = 1) : d201503 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17179 q = 1) (hb : d198467 q = 1) : d201494 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d201494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53589 q ha hb
    | true =>
      simp only [d17179, d201494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17180 q = 1) (hb : d198467 q = 1) : d201495 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d201495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d201495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17185 q = 1) (hb : d198467 q = 1) : d201500 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17185, d201500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17185, d201500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17186 q = 1) (hb : d198467 q = 1) : d201501 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17186, d201501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17186, d201501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17187 q = 1) (hb : d198467 q = 1) : d201502 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17187, d201502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17187, d201502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17188 q = 1) (hb : d198467 q = 1) : d201503 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17188, d201503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17188, d201503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53592 (p : Pattern) (ha : d17194 p = 1) (hb : d198467 p = 1) : d201509 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17189 q = 1) (hb : d198467 q = 1) : d201504 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17189, d201504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53590 q ha hb
    | true =>
      simp only [d17189, d201504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53591 q ha hb
  have h2 (q : Pattern) (ha : d17190 q = 1) (hb : d198467 q = 1) : d201505 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17190, d201505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17190, d201505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17191 q = 1) (hb : d198467 q = 1) : d201506 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17191, d201506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17191, d201506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17192 q = 1) (hb : d198467 q = 1) : d201507 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17192, d201507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17192, d201507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17193 q = 1) (hb : d198467 q = 1) : d201508 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17193, d201508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17193, d201508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17194 q = 1) (hb : d198467 q = 1) : d201509 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17194, d201509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17194, d201509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53593 (p : Pattern) (ha : d17197 p = 1) (hb : d198467 p = 1) : d201512 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17175 q = 1) (hb : d198467 q = 1) : d201490 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17175, d201490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53588 q ha hb
    | true =>
      simp only [d17175, d201490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17176 q = 1) (hb : d198467 q = 1) : d201491 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17176, d201491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17176, d201491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17179 q = 1) (hb : d198467 q = 1) : d201494 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d201494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53589 q ha hb
    | true =>
      simp only [d17179, d201494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17180 q = 1) (hb : d198467 q = 1) : d201495 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d201495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d201495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17181 q = 1) (hb : d198467 q = 1) : d201496 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17181, d201496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17181, d201496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17182 q = 1) (hb : d198467 q = 1) : d201497 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17182, d201497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17182, d201497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17183 q = 1) (hb : d198467 q = 1) : d201498 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17183, d201498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17183, d201498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17197 q = 1) (hb : d198467 q = 1) : d201512 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17197, d201512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17197, d201512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro53594 (p : Pattern) (ha : d17198 p = 1) (hb : d198467 p = 1) : d201513 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17179 q = 1) (hb : d198467 q = 1) : d201494 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d201494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53589 q ha hb
    | true =>
      simp only [d17179, d201494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17180 q = 1) (hb : d198467 q = 1) : d201495 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d201495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d201495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17185 q = 1) (hb : d198467 q = 1) : d201500 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17185, d201500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17185, d201500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17186 q = 1) (hb : d198467 q = 1) : d201501 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17186, d201501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17186, d201501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17187 q = 1) (hb : d198467 q = 1) : d201502 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17187, d201502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17187, d201502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17198 q = 1) (hb : d198467 q = 1) : d201513 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17198, d201513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17198, d201513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53595 (p : Pattern) (ha : d17204 p = 1) (hb : d198467 p = 1) : d201519 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17189 q = 1) (hb : d198467 q = 1) : d201504 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17189, d201504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53590 q ha hb
    | true =>
      simp only [d17189, d201504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53591 q ha hb
  have h2 (q : Pattern) (ha : d17190 q = 1) (hb : d198467 q = 1) : d201505 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17190, d201505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17190, d201505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17191 q = 1) (hb : d198467 q = 1) : d201506 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17191, d201506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17191, d201506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17192 q = 1) (hb : d198467 q = 1) : d201507 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17192, d201507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17192, d201507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17193 q = 1) (hb : d198467 q = 1) : d201508 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17193, d201508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17193, d201508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17199 q = 1) (hb : d198467 q = 1) : d201514 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17199, d201514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53593 q ha hb
    | true =>
      simp only [d17199, d201514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53594 q ha hb
  have h7 (q : Pattern) (ha : d17200 q = 1) (hb : d198467 q = 1) : d201515 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17200, d201515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17200, d201515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17201 q = 1) (hb : d198467 q = 1) : d201516 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17201, d201516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17201, d201516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17202 q = 1) (hb : d198467 q = 1) : d201517 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17202, d201517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17202, d201517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17203 q = 1) (hb : d198467 q = 1) : d201518 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17203, d201518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17203, d201518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17204 q = 1) (hb : d198467 q = 1) : d201519 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17204, d201519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17204, d201519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro53596 (p : Pattern) (ha : d17244 p = 1) (hb : d198467 p = 1) : d201489 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17162 q = 1) (hb : d198467 q = 1) : d201478 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17162, d201478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53584 q ha hb
    | true =>
      simp only [d17162, d201478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53587 q ha hb
  have h2 (q : Pattern) (ha : d17163 q = 1) (hb : d198467 q = 1) : d201479 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17163, d201479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17163, d201479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17164 q = 1) (hb : d198467 q = 1) : d201480 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17164, d201480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17164, d201480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17165 q = 1) (hb : d198467 q = 1) : d201483 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17165, d201483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53587 q ha hb
    | true =>
      simp only [d17165, d201483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53579 q ha hb
  have h5 (q : Pattern) (ha : d17166 q = 1) (hb : d198467 q = 1) : d201484 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17166, d201484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17166, d201484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17167 q = 1) (hb : d198467 q = 1) : d201485 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17167, d201485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17167, d201485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17168 q = 1) (hb : d198467 q = 1) : d201486 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17168, d201486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17168, d201486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17242 q = 1) (hb : d198467 q = 1) : d201487 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17242, d201487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17242, d201487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17243 q = 1) (hb : d198467 q = 1) : d201488 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17243, d201488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17243, d201488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17244 q = 1) (hb : d198467 q = 1) : d201489 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17244, d201489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17244, d201489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro53597 (p : Pattern) (ha : d17254 p = 1) (hb : d198467 p = 1) : d201499 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17245 q = 1) (hb : d198467 q = 1) : d201490 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17245, d201490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53596 q ha hb
    | true =>
      simp only [d17245, d201490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17246 q = 1) (hb : d198467 q = 1) : d201491 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17246, d201491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17246, d201491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17179 q = 1) (hb : d198467 q = 1) : d201494 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d201494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53589 q ha hb
    | true =>
      simp only [d17179, d201494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17180 q = 1) (hb : d198467 q = 1) : d201495 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d201495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d201495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17251 q = 1) (hb : d198467 q = 1) : d201496 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17251, d201496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17251, d201496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17252 q = 1) (hb : d198467 q = 1) : d201497 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17252, d201497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17252, d201497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17253 q = 1) (hb : d198467 q = 1) : d201498 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17253, d201498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17253, d201498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17254 q = 1) (hb : d198467 q = 1) : d201499 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17254, d201499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17254, d201499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53598 (p : Pattern) (ha : d17348 p = 1) (hb : d198467 p = 1) : d201603 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17338 q = 1) (hb : d198467 q = 1) : d201504 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17338, d201504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53597 q ha hb
    | true =>
      simp only [d17338, d201504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53591 q ha hb
  have h2 (q : Pattern) (ha : d17339 q = 1) (hb : d198467 q = 1) : d201505 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17339, d201505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17339, d201505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17340 q = 1) (hb : d198467 q = 1) : d201506 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17340, d201506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17340, d201506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17341 q = 1) (hb : d198467 q = 1) : d201507 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17341, d201507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17341, d201507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17342 q = 1) (hb : d198467 q = 1) : d201508 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17342, d201508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17342, d201508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17343 q = 1) (hb : d198467 q = 1) : d201598 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17343, d201598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53591 q ha hb
    | true =>
      simp only [d17343, d201598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17344 q = 1) (hb : d198467 q = 1) : d201599 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17344, d201599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17344, d201599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17345 q = 1) (hb : d198467 q = 1) : d201600 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17345, d201600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17345, d201600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17346 q = 1) (hb : d198467 q = 1) : d201601 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17346, d201601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17346, d201601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17347 q = 1) (hb : d198467 q = 1) : d201602 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17347, d201602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17347, d201602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17348 q = 1) (hb : d198467 q = 1) : d201603 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17348, d201603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17348, d201603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro53599 (p : Pattern) (ha : d17354 p = 1) (hb : d198467 p = 1) : d201609 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17343 q = 1) (hb : d198467 q = 1) : d201598 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17343, d201598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53591 q ha hb
    | true =>
      simp only [d17343, d201598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17344 q = 1) (hb : d198467 q = 1) : d201599 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17344, d201599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17344, d201599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17345 q = 1) (hb : d198467 q = 1) : d201600 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17345, d201600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17345, d201600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17346 q = 1) (hb : d198467 q = 1) : d201601 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17346, d201601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17346, d201601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17347 q = 1) (hb : d198467 q = 1) : d201602 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17347, d201602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17347, d201602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17349 q = 1) (hb : d198467 q = 1) : d201604 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17349, d201604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53594 q ha hb
    | true =>
      simp only [d17349, d201604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17350 q = 1) (hb : d198467 q = 1) : d201605 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17350, d201605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17350, d201605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17351 q = 1) (hb : d198467 q = 1) : d201606 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17351, d201606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17351, d201606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17352 q = 1) (hb : d198467 q = 1) : d201607 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17352, d201607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17352, d201607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17353 q = 1) (hb : d198467 q = 1) : d201608 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17353, d201608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17353, d201608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17354 q = 1) (hb : d198467 q = 1) : d201609 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17354, d201609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17354, d201609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro53600 (p : Pattern) (ha : d17363 p = 1) (hb : d198467 p = 1) : d201618 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17349 q = 1) (hb : d198467 q = 1) : d201604 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17349, d201604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53594 q ha hb
    | true =>
      simp only [d17349, d201604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17350 q = 1) (hb : d198467 q = 1) : d201605 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17350, d201605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17350, d201605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17351 q = 1) (hb : d198467 q = 1) : d201606 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17351, d201606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17351, d201606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17352 q = 1) (hb : d198467 q = 1) : d201607 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17352, d201607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17352, d201607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17353 q = 1) (hb : d198467 q = 1) : d201608 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17353, d201608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17353, d201608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17363 q = 1) (hb : d198467 q = 1) : d201618 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17363, d201618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17363, d201618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53601 (p : Pattern) (ha : d15813 p = 1) (hb : d198467 p = 1) : d201642 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2346 q = 1) (hb : d198467 q = 1) : d201632 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2346, d201632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2346, d201632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53580 q ha hb
  have h2 (q : Pattern) (ha : d2065 q = 1) (hb : d198467 q = 1) : d201472 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d201472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53580 q ha hb
    | true =>
      simp only [d2065, d201472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2347 q = 1) (hb : d198467 q = 1) : d201633 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2347, d201633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2347, d201633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2066 q = 1) (hb : d198467 q = 1) : d201473 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, d201473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2066, d201473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2348 q = 1) (hb : d198467 q = 1) : d201634 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2348, d201634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2348, d201634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2349 q = 1) (hb : d198467 q = 1) : d201635 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2349, d201635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2349, d201635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2355 q = 1) (hb : d198467 q = 1) : d201641 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2355, d201641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2355, d201641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15794 q = 1) (hb : d198467 q = 1) : d15794 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d15813 q = 1) (hb : d198467 q = 1) : d201642 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15813, d201642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15813, d201642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro53602 (p : Pattern) (ha : d17396 p = 1) (hb : d198467 p = 1) : d201637 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2340 q = 1) (hb : d198467 q = 1) : d13813 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2340, d13813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2340, d13813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53585 q ha hb
  have h2 (q : Pattern) (ha : d2053 q = 1) (hb : d198467 q = 1) : d10353 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2053, d10353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53585 q ha hb
    | true =>
      simp only [d2053, d10353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2341 q = 1) (hb : d198467 q = 1) : d13814 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2341, d13814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2341, d13814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2054 q = 1) (hb : d198467 q = 1) : d10355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2054, d10355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2054, d10355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2342 q = 1) (hb : d198467 q = 1) : d13815 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2342, d13815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2342, d13815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2343 q = 1) (hb : d198467 q = 1) : d13816 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2343, d13816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2343, d13816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17391 q = 1) (hb : d198467 q = 1) : d201632 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17391, d201632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17391, d201632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53586 q ha hb
  have h8 (q : Pattern) (ha : d10391 q = 1) (hb : d198467 q = 1) : d201472 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10391, d201472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53586 q ha hb
    | true =>
      simp only [d10391, d201472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17392 q = 1) (hb : d198467 q = 1) : d201633 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17392, d201633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17392, d201633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10393 q = 1) (hb : d198467 q = 1) : d201473 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10393, d201473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10393, d201473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d17393 q = 1) (hb : d198467 q = 1) : d201634 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17393, d201634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17393, d201634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17394 q = 1) (hb : d198467 q = 1) : d201635 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17394, d201635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17394, d201635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d17395 q = 1) (hb : d198467 q = 1) : d201636 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17395, d201636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17395, d201636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15775 q = 1) (hb : d198467 q = 1) : d13817 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15775, d13817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15775, d13817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53583 q ha hb
  have h15 (q : Pattern) (ha : d10371 q = 1) (hb : d198467 q = 1) : d13678 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, d13678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53583 q ha hb
    | true =>
      simp only [d10371, d13678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d15776 q = 1) (hb : d198467 q = 1) : d13818 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15776, d13818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d15776, d13818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10373 q = 1) (hb : d198467 q = 1) : d13679 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10373, d13679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d10373, d13679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d15777 q = 1) (hb : d198467 q = 1) : d13819 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15777, d13819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d15777, d13819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d15778 q = 1) (hb : d198467 q = 1) : d13820 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15778, d13820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d15778, d13820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d15779 q = 1) (hb : d198467 q = 1) : d22937 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15779, d22937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d15779, d22937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d17396 q = 1) (hb : d198467 q = 1) : d201637 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17396, d201637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d17396, d201637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro53603 (p : Pattern) (ha : d17422 p = 1) (hb : d198467 p = 1) : d201661 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17417 q = 1) (hb : d198467 q = 1) : d201643 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17417, d201643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53602 q ha hb
    | true =>
      simp only [d17417, d201643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53601 q ha hb
  have h2 (q : Pattern) (ha : d17418 q = 1) (hb : d198467 q = 1) : d201644 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17418, d201644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17418, d201644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17419 q = 1) (hb : d198467 q = 1) : d201645 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17419, d201645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17419, d201645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17420 q = 1) (hb : d198467 q = 1) : d201651 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17420, d201651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17420, d201651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17421 q = 1) (hb : d198467 q = 1) : d201660 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17421, d201660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17421, d201660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17422 q = 1) (hb : d198467 q = 1) : d201661 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17422, d201661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17422, d201661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53604 (p : Pattern) (ha : d17494 p = 1) (hb : d198467 p = 1) : d201693 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17423 q = 1) (hb : d198467 q = 1) : d201662 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17423, d201662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53603 q ha hb
    | true =>
      simp only [d17423, d201662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17424 q = 1) (hb : d198467 q = 1) : d201663 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17424, d201663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17424, d201663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17491 q = 1) (hb : d198467 q = 1) : d201690 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17491, d201690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17491, d201690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17492 q = 1) (hb : d198467 q = 1) : d201691 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17492, d201691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17492, d201691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17493 q = 1) (hb : d198467 q = 1) : d201692 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17493, d201692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17493, d201692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17494 q = 1) (hb : d198467 q = 1) : d201693 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17494, d201693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17494, d201693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53605 (p : Pattern) (ha : d17500 p = 1) (hb : d198467 p = 1) : d201699 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17495 q = 1) (hb : d198467 q = 1) : d201694 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17495, d201694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53604 q ha hb
    | true =>
      simp only [d17495, d201694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17496 q = 1) (hb : d198467 q = 1) : d201695 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17496, d201695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17496, d201695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17497 q = 1) (hb : d198467 q = 1) : d201696 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17497, d201696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17497, d201696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17498 q = 1) (hb : d198467 q = 1) : d201697 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17498, d201697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17498, d201697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17499 q = 1) (hb : d198467 q = 1) : d201698 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17499, d201698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17499, d201698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17500 q = 1) (hb : d198467 q = 1) : d201699 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17500, d201699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17500, d201699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53606 (p : Pattern) (ha : d17209 p = 1) (hb : d198467 p = 1) : d201524 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17175 q = 1) (hb : d198467 q = 1) : d201490 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17175, d201490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53588 q ha hb
    | true =>
      simp only [d17175, d201490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17176 q = 1) (hb : d198467 q = 1) : d201491 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17176, d201491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17176, d201491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17179 q = 1) (hb : d198467 q = 1) : d201494 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d201494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53589 q ha hb
    | true =>
      simp only [d17179, d201494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17180 q = 1) (hb : d198467 q = 1) : d201495 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d201495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d201495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17181 q = 1) (hb : d198467 q = 1) : d201496 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17181, d201496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17181, d201496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17182 q = 1) (hb : d198467 q = 1) : d201497 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17182, d201497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17182, d201497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17208 q = 1) (hb : d198467 q = 1) : d201523 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17208, d201523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17208, d201523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17209 q = 1) (hb : d198467 q = 1) : d201524 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17209, d201524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17209, d201524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53607 (p : Pattern) (ha : d17211 p = 1) (hb : d198467 p = 1) : d201526 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17179 q = 1) (hb : d198467 q = 1) : d201494 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d201494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53589 q ha hb
    | true =>
      simp only [d17179, d201494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17180 q = 1) (hb : d198467 q = 1) : d201495 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d201495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d201495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17185 q = 1) (hb : d198467 q = 1) : d201500 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17185, d201500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17185, d201500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17186 q = 1) (hb : d198467 q = 1) : d201501 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17186, d201501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17186, d201501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17210 q = 1) (hb : d198467 q = 1) : d201525 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17210, d201525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17210, d201525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17211 q = 1) (hb : d198467 q = 1) : d201526 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17211, d201526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17211, d201526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53608 (p : Pattern) (ha : d17218 p = 1) (hb : d198467 p = 1) : d201533 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17175 q = 1) (hb : d198467 q = 1) : d201490 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17175, d201490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53588 q ha hb
    | true =>
      simp only [d17175, d201490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17176 q = 1) (hb : d198467 q = 1) : d201491 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17176, d201491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17176, d201491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17179 q = 1) (hb : d198467 q = 1) : d201494 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d201494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53589 q ha hb
    | true =>
      simp only [d17179, d201494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17180 q = 1) (hb : d198467 q = 1) : d201495 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d201495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d201495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17181 q = 1) (hb : d198467 q = 1) : d201496 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17181, d201496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17181, d201496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17216 q = 1) (hb : d198467 q = 1) : d201531 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17216, d201531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17216, d201531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17217 q = 1) (hb : d198467 q = 1) : d201532 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17217, d201532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17217, d201532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17218 q = 1) (hb : d198467 q = 1) : d201533 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17218, d201533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17218, d201533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53609 (p : Pattern) (ha : d17221 p = 1) (hb : d198467 p = 1) : d201536 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17179 q = 1) (hb : d198467 q = 1) : d201494 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d201494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53589 q ha hb
    | true =>
      simp only [d17179, d201494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17180 q = 1) (hb : d198467 q = 1) : d201495 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d201495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d201495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17185 q = 1) (hb : d198467 q = 1) : d201500 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17185, d201500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17185, d201500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17219 q = 1) (hb : d198467 q = 1) : d201534 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17219, d201534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17219, d201534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17220 q = 1) (hb : d198467 q = 1) : d201535 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17220, d201535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17220, d201535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17221 q = 1) (hb : d198467 q = 1) : d201536 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17221, d201536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17221, d201536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53610 (p : Pattern) (ha : d2143 p = 1) (hb : d198467 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2012 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2143 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d2143, d198467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2143, d198467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro53611 (p : Pattern) (ha : d17229 p = 1) (hb : d198467 p = 1) : d196934 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2144 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53610 q ha hb
    | true =>
      simp only [d2144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2145 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2146 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2147 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10343 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47361 q ha hb
    | true =>
      simp only [d10343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10345 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17225 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17226 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17227 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17228 q = 1) (hb : d198467 q = 1) : d17228 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d17229 q = 1) (hb : d198467 q = 1) : d196934 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17229, d196934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17229, d196934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro53612 (p : Pattern) (ha : d17233 p = 1) (hb : d198467 p = 1) : d22772 p = 1 := by
  have h0 (q : Pattern) (ha : d13676 q = 1) (hb : d198467 q = 1) : d13676 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10371 q = 1) (hb : d198467 q = 1) : d13678 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, d13678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53583 q ha hb
    | true =>
      simp only [d10371, d13678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10373 q = 1) (hb : d198467 q = 1) : d13679 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10373, d13679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10373, d13679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d15548 q = 1) (hb : d198467 q = 1) : d13680 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15548, d13680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15548, d13680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15549 q = 1) (hb : d198467 q = 1) : d13681 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15549, d13681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15549, d13681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d17156 q = 1) (hb : d198467 q = 1) : d13682 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17156, d13682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17156, d13682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15550 q = 1) (hb : d198467 q = 1) : d22693 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15550, d22693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15550, d22693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d17233 q = 1) (hb : d198467 q = 1) : d22772 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17233, d22772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17233, d22772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53613 (p : Pattern) (ha : d17239 p = 1) (hb : d198467 p = 1) : d201548 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17230 q = 1) (hb : d198467 q = 1) : d201540 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17230, d201540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53611 q ha hb
    | true =>
      simp only [d17230, d201540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53584 q ha hb
  have h2 (q : Pattern) (ha : d17231 q = 1) (hb : d198467 q = 1) : d201541 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17231, d201541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17231, d201541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17232 q = 1) (hb : d198467 q = 1) : d201542 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17232, d201542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17232, d201542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17234 q = 1) (hb : d198467 q = 1) : d201543 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17234, d201543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53584 q ha hb
    | true =>
      simp only [d17234, d201543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53612 q ha hb
  have h5 (q : Pattern) (ha : d17235 q = 1) (hb : d198467 q = 1) : d201544 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17235, d201544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17235, d201544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17236 q = 1) (hb : d198467 q = 1) : d201545 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17236, d201545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17236, d201545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17237 q = 1) (hb : d198467 q = 1) : d201546 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17237, d201546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17237, d201546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17162 q = 1) (hb : d198467 q = 1) : d201478 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17162, d201478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53584 q ha hb
    | true =>
      simp only [d17162, d201478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53587 q ha hb
  have h9 (q : Pattern) (ha : d17163 q = 1) (hb : d198467 q = 1) : d201479 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17163, d201479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17163, d201479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17164 q = 1) (hb : d198467 q = 1) : d201480 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17164, d201480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17164, d201480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17165 q = 1) (hb : d198467 q = 1) : d201483 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17165, d201483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53587 q ha hb
    | true =>
      simp only [d17165, d201483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53579 q ha hb
  have h12 (q : Pattern) (ha : d17166 q = 1) (hb : d198467 q = 1) : d201484 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17166, d201484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17166, d201484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17167 q = 1) (hb : d198467 q = 1) : d201485 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17167, d201485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17167, d201485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d17168 q = 1) (hb : d198467 q = 1) : d201486 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17168, d201486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17168, d201486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17238 q = 1) (hb : d198467 q = 1) : d201547 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17238, d201547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17238, d201547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d17239 q = 1) (hb : d198467 q = 1) : d201548 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17239, d201548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d17239, d201548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro53614 (p : Pattern) (ha : d17250 p = 1) (hb : d198467 p = 1) : d201554 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17240 q = 1) (hb : d198467 q = 1) : d201549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17240, d201549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53613 q ha hb
    | true =>
      simp only [d17240, d201549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17241 q = 1) (hb : d198467 q = 1) : d201550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17241, d201550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17241, d201550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17245 q = 1) (hb : d198467 q = 1) : d201490 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17245, d201490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53596 q ha hb
    | true =>
      simp only [d17245, d201490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17246 q = 1) (hb : d198467 q = 1) : d201491 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17246, d201491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17246, d201491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17247 q = 1) (hb : d198467 q = 1) : d201551 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17247, d201551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17247, d201551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17248 q = 1) (hb : d198467 q = 1) : d201552 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17248, d201552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17248, d201552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17249 q = 1) (hb : d198467 q = 1) : d201553 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17249, d201553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17249, d201553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17250 q = 1) (hb : d198467 q = 1) : d201554 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17250, d201554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17250, d201554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53615 (p : Pattern) (ha : d13614 p = 1) (hb : d198467 p = 1) : d201557 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2065 q = 1) (hb : d198467 q = 1) : d201472 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d201472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53580 q ha hb
    | true =>
      simp only [d2065, d201472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2066 q = 1) (hb : d198467 q = 1) : d201473 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, d201473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2066, d201473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2067 q = 1) (hb : d198467 q = 1) : d201474 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2067, d201474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2067, d201474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2068 q = 1) (hb : d198467 q = 1) : d201475 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2068, d201475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2068, d201475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2071 q = 1) (hb : d198467 q = 1) : d201481 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2071, d201481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2071, d201481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13614 q = 1) (hb : d198467 q = 1) : d201557 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13614, d201557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13614, d201557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53616 (p : Pattern) (ha : d17299 p = 1) (hb : d198467 p = 1) : d201563 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17162 q = 1) (hb : d198467 q = 1) : d201478 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17162, d201478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53584 q ha hb
    | true =>
      simp only [d17162, d201478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53587 q ha hb
  have h2 (q : Pattern) (ha : d17163 q = 1) (hb : d198467 q = 1) : d201479 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17163, d201479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17163, d201479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17164 q = 1) (hb : d198467 q = 1) : d201480 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17164, d201480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17164, d201480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17165 q = 1) (hb : d198467 q = 1) : d201483 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17165, d201483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53587 q ha hb
    | true =>
      simp only [d17165, d201483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53579 q ha hb
  have h5 (q : Pattern) (ha : d17166 q = 1) (hb : d198467 q = 1) : d201484 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17166, d201484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17166, d201484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17167 q = 1) (hb : d198467 q = 1) : d201485 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17167, d201485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17167, d201485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17168 q = 1) (hb : d198467 q = 1) : d201486 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17168, d201486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17168, d201486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17294 q = 1) (hb : d198467 q = 1) : d201558 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17294, d201558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53587 q ha hb
    | true =>
      simp only [d17294, d201558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53615 q ha hb
  have h9 (q : Pattern) (ha : d17295 q = 1) (hb : d198467 q = 1) : d201559 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17295, d201559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17295, d201559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17296 q = 1) (hb : d198467 q = 1) : d201560 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17296, d201560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17296, d201560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17297 q = 1) (hb : d198467 q = 1) : d201561 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17297, d201561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17297, d201561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d17298 q = 1) (hb : d198467 q = 1) : d201562 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17298, d201562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17298, d201562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17299 q = 1) (hb : d198467 q = 1) : d201563 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17299, d201563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17299, d201563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro53617 (p : Pattern) (ha : d17305 p = 1) (hb : d198467 p = 1) : d201569 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17300 q = 1) (hb : d198467 q = 1) : d201564 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17300, d201564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53616 q ha hb
    | true =>
      simp only [d17300, d201564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17301 q = 1) (hb : d198467 q = 1) : d201565 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17301, d201565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17301, d201565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17302 q = 1) (hb : d198467 q = 1) : d201566 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17302, d201566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17302, d201566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17303 q = 1) (hb : d198467 q = 1) : d201567 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17303, d201567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17303, d201567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17304 q = 1) (hb : d198467 q = 1) : d201568 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17304, d201568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17304, d201568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17305 q = 1) (hb : d198467 q = 1) : d201569 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17305, d201569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17305, d201569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53618 (p : Pattern) (ha : d128400 p = 1) (hb : d198467 p = 1) : d201575 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17212 q = 1) (hb : d198467 q = 1) : d201527 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17212, d201527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53606 q ha hb
    | true =>
      simp only [d17212, d201527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53607 q ha hb
  have h2 (q : Pattern) (ha : d17213 q = 1) (hb : d198467 q = 1) : d201528 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17213, d201528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17213, d201528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17214 q = 1) (hb : d198467 q = 1) : d201529 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17214, d201529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17214, d201529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17215 q = 1) (hb : d198467 q = 1) : d201530 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17215, d201530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17215, d201530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17222 q = 1) (hb : d198467 q = 1) : d201537 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17222, d201537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53608 q ha hb
    | true =>
      simp only [d17222, d201537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53609 q ha hb
  have h6 (q : Pattern) (ha : d17223 q = 1) (hb : d198467 q = 1) : d201538 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17223, d201538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17223, d201538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17224 q = 1) (hb : d198467 q = 1) : d201539 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17224, d201539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17224, d201539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17255 q = 1) (hb : d198467 q = 1) : d201555 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17255, d201555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53614 q ha hb
    | true =>
      simp only [d17255, d201555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53597 q ha hb
  have h9 (q : Pattern) (ha : d128396 q = 1) (hb : d198467 q = 1) : d201556 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128396, d201556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128396, d201556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d17306 q = 1) (hb : d198467 q = 1) : d201570 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17306, d201570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53617 q ha hb
    | true =>
      simp only [d17306, d201570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d17307 q = 1) (hb : d198467 q = 1) : d201571 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17307, d201571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17307, d201571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128397 q = 1) (hb : d198467 q = 1) : d201572 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128397, d201572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128397, d201572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128398 q = 1) (hb : d198467 q = 1) : d201573 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128398, d201573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128398, d201573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128399 q = 1) (hb : d198467 q = 1) : d201574 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128399, d201574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128399, d201574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128400 q = 1) (hb : d198467 q = 1) : d201575 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128400, d201575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128400, d201575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro53619 (p : Pattern) (ha : d17312 p = 1) (hb : d198467 p = 1) : d201576 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17175 q = 1) (hb : d198467 q = 1) : d201490 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17175, d201490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53588 q ha hb
    | true =>
      simp only [d17175, d201490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17176 q = 1) (hb : d198467 q = 1) : d201491 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17176, d201491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17176, d201491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17179 q = 1) (hb : d198467 q = 1) : d201494 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d201494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53589 q ha hb
    | true =>
      simp only [d17179, d201494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17180 q = 1) (hb : d198467 q = 1) : d201495 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d201495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d201495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17181 q = 1) (hb : d198467 q = 1) : d201496 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17181, d201496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17181, d201496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17182 q = 1) (hb : d198467 q = 1) : d201497 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17182, d201497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17182, d201497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17208 q = 1) (hb : d198467 q = 1) : d201523 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17208, d201523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17208, d201523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17312 q = 1) (hb : d198467 q = 1) : d201576 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17312, d201576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17312, d201576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro53620 (p : Pattern) (ha : d17313 p = 1) (hb : d198467 p = 1) : d201577 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17179 q = 1) (hb : d198467 q = 1) : d201494 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d201494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53589 q ha hb
    | true =>
      simp only [d17179, d201494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17180 q = 1) (hb : d198467 q = 1) : d201495 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d201495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d201495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17185 q = 1) (hb : d198467 q = 1) : d201500 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17185, d201500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17185, d201500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17186 q = 1) (hb : d198467 q = 1) : d201501 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17186, d201501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17186, d201501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17210 q = 1) (hb : d198467 q = 1) : d201525 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17210, d201525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17210, d201525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17313 q = 1) (hb : d198467 q = 1) : d201577 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17313, d201577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17313, d201577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53621 (p : Pattern) (ha : d17318 p = 1) (hb : d198467 p = 1) : d201582 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17175 q = 1) (hb : d198467 q = 1) : d201490 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17175, d201490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53588 q ha hb
    | true =>
      simp only [d17175, d201490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17176 q = 1) (hb : d198467 q = 1) : d201491 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17176, d201491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17176, d201491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17179 q = 1) (hb : d198467 q = 1) : d201494 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d201494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53589 q ha hb
    | true =>
      simp only [d17179, d201494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17180 q = 1) (hb : d198467 q = 1) : d201495 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d201495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d201495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17181 q = 1) (hb : d198467 q = 1) : d201496 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17181, d201496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17181, d201496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17216 q = 1) (hb : d198467 q = 1) : d201531 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17216, d201531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17216, d201531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17217 q = 1) (hb : d198467 q = 1) : d201532 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17217, d201532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17217, d201532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17318 q = 1) (hb : d198467 q = 1) : d201582 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17318, d201582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17318, d201582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro53622 (p : Pattern) (ha : d17319 p = 1) (hb : d198467 p = 1) : d201583 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17179 q = 1) (hb : d198467 q = 1) : d201494 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d201494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53589 q ha hb
    | true =>
      simp only [d17179, d201494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17180 q = 1) (hb : d198467 q = 1) : d201495 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d201495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d201495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17185 q = 1) (hb : d198467 q = 1) : d201500 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17185, d201500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17185, d201500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17219 q = 1) (hb : d198467 q = 1) : d201534 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17219, d201534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17219, d201534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17220 q = 1) (hb : d198467 q = 1) : d201535 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17220, d201535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17220, d201535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17319 q = 1) (hb : d198467 q = 1) : d201583 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17319, d201583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17319, d201583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53623 (p : Pattern) (ha : d17323 p = 1) (hb : d198467 p = 1) : d201587 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17240 q = 1) (hb : d198467 q = 1) : d201549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17240, d201549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53613 q ha hb
    | true =>
      simp only [d17240, d201549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17241 q = 1) (hb : d198467 q = 1) : d201550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17241, d201550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17241, d201550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17245 q = 1) (hb : d198467 q = 1) : d201490 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17245, d201490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53596 q ha hb
    | true =>
      simp only [d17245, d201490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17246 q = 1) (hb : d198467 q = 1) : d201491 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17246, d201491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17246, d201491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17247 q = 1) (hb : d198467 q = 1) : d201551 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17247, d201551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17247, d201551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17248 q = 1) (hb : d198467 q = 1) : d201552 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17248, d201552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17248, d201552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17249 q = 1) (hb : d198467 q = 1) : d201553 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17249, d201553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17249, d201553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17323 q = 1) (hb : d198467 q = 1) : d201587 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17323, d201587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17323, d201587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro53624 (p : Pattern) (ha : d17324 p = 1) (hb : d198467 p = 1) : d201512 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17245 q = 1) (hb : d198467 q = 1) : d201490 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17245, d201490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53596 q ha hb
    | true =>
      simp only [d17245, d201490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17246 q = 1) (hb : d198467 q = 1) : d201491 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17246, d201491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17246, d201491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17179 q = 1) (hb : d198467 q = 1) : d201494 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d201494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53589 q ha hb
    | true =>
      simp only [d17179, d201494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17180 q = 1) (hb : d198467 q = 1) : d201495 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d201495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d201495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17251 q = 1) (hb : d198467 q = 1) : d201496 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17251, d201496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17251, d201496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17252 q = 1) (hb : d198467 q = 1) : d201497 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17252, d201497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17252, d201497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17253 q = 1) (hb : d198467 q = 1) : d201498 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17253, d201498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17253, d201498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17324 q = 1) (hb : d198467 q = 1) : d201512 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17324, d201512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17324, d201512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro53625 (p : Pattern) (ha : d17330 p = 1) (hb : d198467 p = 1) : d201590 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17300 q = 1) (hb : d198467 q = 1) : d201564 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17300, d201564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53616 q ha hb
    | true =>
      simp only [d17300, d201564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17301 q = 1) (hb : d198467 q = 1) : d201565 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17301, d201565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17301, d201565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17302 q = 1) (hb : d198467 q = 1) : d201566 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17302, d201566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17302, d201566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17303 q = 1) (hb : d198467 q = 1) : d201567 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17303, d201567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17303, d201567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17304 q = 1) (hb : d198467 q = 1) : d201568 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17304, d201568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17304, d201568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17330 q = 1) (hb : d198467 q = 1) : d201590 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17330, d201590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17330, d201590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53626 (p : Pattern) (ha : d128405 p = 1) (hb : d198467 p = 1) : d201596 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17212 q = 1) (hb : d198467 q = 1) : d201527 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17212, d201527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53606 q ha hb
    | true =>
      simp only [d17212, d201527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53607 q ha hb
  have h2 (q : Pattern) (ha : d17213 q = 1) (hb : d198467 q = 1) : d201528 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17213, d201528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17213, d201528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17214 q = 1) (hb : d198467 q = 1) : d201529 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17214, d201529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17214, d201529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17215 q = 1) (hb : d198467 q = 1) : d201530 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17215, d201530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17215, d201530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17222 q = 1) (hb : d198467 q = 1) : d201537 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17222, d201537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53608 q ha hb
    | true =>
      simp only [d17222, d201537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53609 q ha hb
  have h6 (q : Pattern) (ha : d17223 q = 1) (hb : d198467 q = 1) : d201538 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17223, d201538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17223, d201538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17224 q = 1) (hb : d198467 q = 1) : d201539 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17224, d201539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17224, d201539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17255 q = 1) (hb : d198467 q = 1) : d201555 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17255, d201555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53614 q ha hb
    | true =>
      simp only [d17255, d201555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53597 q ha hb
  have h9 (q : Pattern) (ha : d128396 q = 1) (hb : d198467 q = 1) : d201556 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128396, d201556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128396, d201556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d17306 q = 1) (hb : d198467 q = 1) : d201570 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17306, d201570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53617 q ha hb
    | true =>
      simp only [d17306, d201570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d17307 q = 1) (hb : d198467 q = 1) : d201571 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17307, d201571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17307, d201571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128397 q = 1) (hb : d198467 q = 1) : d201572 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128397, d201572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128397, d201572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128398 q = 1) (hb : d198467 q = 1) : d201573 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128398, d201573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128398, d201573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128399 q = 1) (hb : d198467 q = 1) : d201574 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128399, d201574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128399, d201574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17314 q = 1) (hb : d198467 q = 1) : d201578 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17314, d201578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53619 q ha hb
    | true =>
      simp only [d17314, d201578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53620 q ha hb
  have h16 (q : Pattern) (ha : d17315 q = 1) (hb : d198467 q = 1) : d201579 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17315, d201579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17315, d201579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d17316 q = 1) (hb : d198467 q = 1) : d201580 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17316, d201580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d17316, d201580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d17317 q = 1) (hb : d198467 q = 1) : d201581 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17317, d201581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17317, d201581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d17320 q = 1) (hb : d198467 q = 1) : d201584 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17320, d201584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53621 q ha hb
    | true =>
      simp only [d17320, d201584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53622 q ha hb
  have h20 (q : Pattern) (ha : d17321 q = 1) (hb : d198467 q = 1) : d201585 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17321, d201585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17321, d201585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d17322 q = 1) (hb : d198467 q = 1) : d201586 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17322, d201586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d17322, d201586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d17325 q = 1) (hb : d198467 q = 1) : d201588 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17325, d201588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53623 q ha hb
    | true =>
      simp only [d17325, d201588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53624 q ha hb
  have h23 (q : Pattern) (ha : d128401 q = 1) (hb : d198467 q = 1) : d201589 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128401, d201589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d128401, d201589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d17331 q = 1) (hb : d198467 q = 1) : d201591 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17331, d201591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53625 q ha hb
    | true =>
      simp only [d17331, d201591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d17332 q = 1) (hb : d198467 q = 1) : d201592 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17332, d201592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d17332, d201592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d128402 q = 1) (hb : d198467 q = 1) : d201593 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128402, d201593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d128402, d201593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d128403 q = 1) (hb : d198467 q = 1) : d201594 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128403, d201594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128403, d201594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d128404 q = 1) (hb : d198467 q = 1) : d201595 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128404, d201595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d128404, d201595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d128405 q = 1) (hb : d198467 q = 1) : d201596 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128405, d201596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128405, d201596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro53627 (p : Pattern) (ha : d128412 p = 1) (hb : d198467 p = 1) : d201616 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17325 q = 1) (hb : d198467 q = 1) : d201588 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17325, d201588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53623 q ha hb
    | true =>
      simp only [d17325, d201588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53624 q ha hb
  have h2 (q : Pattern) (ha : d128401 q = 1) (hb : d198467 q = 1) : d201589 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128401, d201589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128401, d201589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17331 q = 1) (hb : d198467 q = 1) : d201591 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17331, d201591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53625 q ha hb
    | true =>
      simp only [d17331, d201591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17332 q = 1) (hb : d198467 q = 1) : d201592 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17332, d201592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17332, d201592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128402 q = 1) (hb : d198467 q = 1) : d201593 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128402, d201593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128402, d201593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128410 q = 1) (hb : d198467 q = 1) : d201614 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128410, d201614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128410, d201614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128411 q = 1) (hb : d198467 q = 1) : d201615 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128411, d201615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128411, d201615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128412 q = 1) (hb : d198467 q = 1) : d201616 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128412, d201616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128412, d201616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53628 (p : Pattern) (ha : d15795 p = 1) (hb : d198467 p = 1) : d201642 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6643 q = 1) (hb : d198467 q = 1) : d201632 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d6643, d201632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6643, d201632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53578 q ha hb
  have h2 (q : Pattern) (ha : d5247 q = 1) (hb : d198467 q = 1) : d201472 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5247, d201472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53578 q ha hb
    | true =>
      simp only [d5247, d201472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6644 q = 1) (hb : d198467 q = 1) : d201633 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d6644, d201633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6644, d201633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5248 q = 1) (hb : d198467 q = 1) : d201473 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5248, d201473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5248, d201473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6645 q = 1) (hb : d198467 q = 1) : d201634 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d6645, d201634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6645, d201634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6646 q = 1) (hb : d198467 q = 1) : d201635 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d6646, d201635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6646, d201635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6647 q = 1) (hb : d198467 q = 1) : d201641 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d6647, d201641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6647, d201641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15794 q = 1) (hb : d198467 q = 1) : d15794 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d15795 q = 1) (hb : d198467 q = 1) : d201642 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15795, d201642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15795, d201642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro53629 (p : Pattern) (ha : d17375 p = 1) (hb : d198467 p = 1) : d197015 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2331 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53610 q ha hb
  have h2 (q : Pattern) (ha : d2144 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53610 q ha hb
    | true =>
      simp only [d2144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2332 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2145 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2333 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2334 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17369 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47361 q ha hb
  have h8 (q : Pattern) (ha : d10343 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47361 q ha hb
    | true =>
      simp only [d10343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17370 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10345 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d17371 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17372 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d17373 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d17374 q = 1) (hb : d198467 q = 1) : d17374 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d17375 q = 1) (hb : d198467 q = 1) : d197015 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17375, d197015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d17375, d197015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro53630 (p : Pattern) (ha : d17382 p = 1) (hb : d198467 p = 1) : d201624 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2335 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53582 q ha hb
  have h2 (q : Pattern) (ha : d2035 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53582 q ha hb
    | true =>
      simp only [d2035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2336 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2036 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2337 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2338 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17376 q = 1) (hb : d198467 q = 1) : d13813 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17376, d13813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17376, d13813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47362 q ha hb
  have h8 (q : Pattern) (ha : d10364 q = 1) (hb : d198467 q = 1) : d10353 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10364, d10353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47362 q ha hb
    | true =>
      simp only [d10364, d10353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17377 q = 1) (hb : d198467 q = 1) : d13814 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17377, d13814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17377, d13814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10366 q = 1) (hb : d198467 q = 1) : d10355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10366, d10355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10366, d10355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d17378 q = 1) (hb : d198467 q = 1) : d13815 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17378, d13815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17378, d13815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17379 q = 1) (hb : d198467 q = 1) : d13816 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17379, d13816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17379, d13816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d17380 q = 1) (hb : d198467 q = 1) : d17374 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17380, d17374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17380, d17374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13816 q = 1) (hb : d198467 q = 1) : d13816 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d15775 q = 1) (hb : d198467 q = 1) : d13817 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15775, d13817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15775, d13817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53583 q ha hb
  have h16 (q : Pattern) (ha : d10371 q = 1) (hb : d198467 q = 1) : d13678 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, d13678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53583 q ha hb
    | true =>
      simp only [d10371, d13678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d15776 q = 1) (hb : d198467 q = 1) : d13818 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15776, d13818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d15776, d13818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d10373 q = 1) (hb : d198467 q = 1) : d13679 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10373, d13679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10373, d13679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d15777 q = 1) (hb : d198467 q = 1) : d13819 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15777, d13819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d15777, d13819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d15778 q = 1) (hb : d198467 q = 1) : d13820 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15778, d13820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d15778, d13820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d17381 q = 1) (hb : d198467 q = 1) : d13821 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17381, d13821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d17381, d13821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d17382 q = 1) (hb : d198467 q = 1) : d201624 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17382, d201624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d17382, d201624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro53631 (p : Pattern) (ha : d17386 p = 1) (hb : d198467 p = 1) : d22938 p = 1 := by
  have h0 (q : Pattern) (ha : d13816 q = 1) (hb : d198467 q = 1) : d13816 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15775 q = 1) (hb : d198467 q = 1) : d13817 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15775, d13817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15775, d13817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53583 q ha hb
  have h3 (q : Pattern) (ha : d10371 q = 1) (hb : d198467 q = 1) : d13678 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, d13678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53583 q ha hb
    | true =>
      simp only [d10371, d13678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d15776 q = 1) (hb : d198467 q = 1) : d13818 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15776, d13818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15776, d13818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10373 q = 1) (hb : d198467 q = 1) : d13679 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10373, d13679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10373, d13679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d15777 q = 1) (hb : d198467 q = 1) : d13819 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15777, d13819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15777, d13819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15778 q = 1) (hb : d198467 q = 1) : d13820 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15778, d13820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15778, d13820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d17381 q = 1) (hb : d198467 q = 1) : d13821 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17381, d13821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17381, d13821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15779 q = 1) (hb : d198467 q = 1) : d22937 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15779, d22937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15779, d22937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d17386 q = 1) (hb : d198467 q = 1) : d22938 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17386, d22938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d17386, d22938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro53632 (p : Pattern) (ha : d17405 p = 1) (hb : d198467 p = 1) : d201648 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17383 q = 1) (hb : d198467 q = 1) : d201625 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17383, d201625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53629 q ha hb
    | true =>
      simp only [d17383, d201625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53630 q ha hb
  have h2 (q : Pattern) (ha : d17384 q = 1) (hb : d198467 q = 1) : d201626 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17384, d201626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17384, d201626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17385 q = 1) (hb : d198467 q = 1) : d201627 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17385, d201627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17385, d201627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17387 q = 1) (hb : d198467 q = 1) : d201628 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17387, d201628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53630 q ha hb
    | true =>
      simp only [d17387, d201628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53631 q ha hb
  have h5 (q : Pattern) (ha : d17388 q = 1) (hb : d198467 q = 1) : d201629 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17388, d201629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17388, d201629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17389 q = 1) (hb : d198467 q = 1) : d201630 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17389, d201630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17389, d201630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17390 q = 1) (hb : d198467 q = 1) : d201631 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17390, d201631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17390, d201631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17397 q = 1) (hb : d198467 q = 1) : d201638 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17397, d201638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53630 q ha hb
    | true =>
      simp only [d17397, d201638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53602 q ha hb
  have h9 (q : Pattern) (ha : d17398 q = 1) (hb : d198467 q = 1) : d201639 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17398, d201639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17398, d201639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17399 q = 1) (hb : d198467 q = 1) : d201640 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17399, d201640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17399, d201640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17400 q = 1) (hb : d198467 q = 1) : d201643 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17400, d201643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53602 q ha hb
    | true =>
      simp only [d17400, d201643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53628 q ha hb
  have h12 (q : Pattern) (ha : d17401 q = 1) (hb : d198467 q = 1) : d201644 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17401, d201644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17401, d201644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17402 q = 1) (hb : d198467 q = 1) : d201645 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17402, d201645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17402, d201645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d17403 q = 1) (hb : d198467 q = 1) : d201646 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17403, d201646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17403, d201646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17404 q = 1) (hb : d198467 q = 1) : d201647 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17404, d201647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17404, d201647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d17405 q = 1) (hb : d198467 q = 1) : d201648 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17405, d201648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d17405, d201648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro53633 (p : Pattern) (ha : d17410 p = 1) (hb : d198467 p = 1) : d201653 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17397 q = 1) (hb : d198467 q = 1) : d201638 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17397, d201638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53630 q ha hb
    | true =>
      simp only [d17397, d201638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53602 q ha hb
  have h2 (q : Pattern) (ha : d17398 q = 1) (hb : d198467 q = 1) : d201639 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17398, d201639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17398, d201639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17399 q = 1) (hb : d198467 q = 1) : d201640 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17399, d201640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17399, d201640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17400 q = 1) (hb : d198467 q = 1) : d201643 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17400, d201643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53602 q ha hb
    | true =>
      simp only [d17400, d201643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53628 q ha hb
  have h5 (q : Pattern) (ha : d17401 q = 1) (hb : d198467 q = 1) : d201644 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17401, d201644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17401, d201644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17402 q = 1) (hb : d198467 q = 1) : d201645 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17402, d201645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17402, d201645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17403 q = 1) (hb : d198467 q = 1) : d201646 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17403, d201646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17403, d201646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17408 q = 1) (hb : d198467 q = 1) : d201651 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17408, d201651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17408, d201651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17409 q = 1) (hb : d198467 q = 1) : d201652 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17409, d201652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17409, d201652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17410 q = 1) (hb : d198467 q = 1) : d201653 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17410, d201653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17410, d201653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro53634 (p : Pattern) (ha : d17416 p = 1) (hb : d198467 p = 1) : d201659 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17406 q = 1) (hb : d198467 q = 1) : d201649 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17406, d201649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53632 q ha hb
    | true =>
      simp only [d17406, d201649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17407 q = 1) (hb : d198467 q = 1) : d201650 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17407, d201650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17407, d201650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17411 q = 1) (hb : d198467 q = 1) : d201654 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17411, d201654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53633 q ha hb
    | true =>
      simp only [d17411, d201654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17412 q = 1) (hb : d198467 q = 1) : d201655 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17412, d201655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17412, d201655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17413 q = 1) (hb : d198467 q = 1) : d201656 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17413, d201656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17413, d201656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17414 q = 1) (hb : d198467 q = 1) : d201657 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17414, d201657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17414, d201657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17415 q = 1) (hb : d198467 q = 1) : d201658 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17415, d201658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17415, d201658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17416 q = 1) (hb : d198467 q = 1) : d201659 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17416, d201659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17416, d201659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro53635 (p : Pattern) (ha : d17428 p = 1) (hb : d198467 p = 1) : d201667 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17411 q = 1) (hb : d198467 q = 1) : d201654 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17411, d201654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53633 q ha hb
    | true =>
      simp only [d17411, d201654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17412 q = 1) (hb : d198467 q = 1) : d201655 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17412, d201655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17412, d201655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17423 q = 1) (hb : d198467 q = 1) : d201662 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17423, d201662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53603 q ha hb
    | true =>
      simp only [d17423, d201662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17424 q = 1) (hb : d198467 q = 1) : d201663 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17424, d201663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17424, d201663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17425 q = 1) (hb : d198467 q = 1) : d201664 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17425, d201664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17425, d201664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17426 q = 1) (hb : d198467 q = 1) : d201665 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17426, d201665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17426, d201665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17427 q = 1) (hb : d198467 q = 1) : d201666 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17427, d201666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17427, d201666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17428 q = 1) (hb : d198467 q = 1) : d201667 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17428, d201667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17428, d201667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro53636 (p : Pattern) (ha : d13843 p = 1) (hb : d198467 p = 1) : d201670 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2346 q = 1) (hb : d198467 q = 1) : d201632 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2346, d201632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2346, d201632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53580 q ha hb
  have h2 (q : Pattern) (ha : d2065 q = 1) (hb : d198467 q = 1) : d201472 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d201472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53580 q ha hb
    | true =>
      simp only [d2065, d201472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2347 q = 1) (hb : d198467 q = 1) : d201633 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2347, d201633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2347, d201633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2066 q = 1) (hb : d198467 q = 1) : d201473 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, d201473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2066, d201473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2348 q = 1) (hb : d198467 q = 1) : d201634 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2348, d201634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2348, d201634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2349 q = 1) (hb : d198467 q = 1) : d201635 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2349, d201635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2349, d201635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2355 q = 1) (hb : d198467 q = 1) : d201641 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2355, d201641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2355, d201641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13843 q = 1) (hb : d198467 q = 1) : d201670 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13843, d201670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13843, d201670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro53637 (p : Pattern) (ha : d17477 p = 1) (hb : d198467 p = 1) : d201676 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17397 q = 1) (hb : d198467 q = 1) : d201638 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17397, d201638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53630 q ha hb
    | true =>
      simp only [d17397, d201638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53602 q ha hb
  have h2 (q : Pattern) (ha : d17398 q = 1) (hb : d198467 q = 1) : d201639 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17398, d201639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17398, d201639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17399 q = 1) (hb : d198467 q = 1) : d201640 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17399, d201640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17399, d201640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17400 q = 1) (hb : d198467 q = 1) : d201643 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17400, d201643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53602 q ha hb
    | true =>
      simp only [d17400, d201643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53628 q ha hb
  have h5 (q : Pattern) (ha : d17401 q = 1) (hb : d198467 q = 1) : d201644 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17401, d201644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17401, d201644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17402 q = 1) (hb : d198467 q = 1) : d201645 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17402, d201645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17402, d201645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17403 q = 1) (hb : d198467 q = 1) : d201646 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17403, d201646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17403, d201646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17472 q = 1) (hb : d198467 q = 1) : d201671 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17472, d201671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53602 q ha hb
    | true =>
      simp only [d17472, d201671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53636 q ha hb
  have h9 (q : Pattern) (ha : d17473 q = 1) (hb : d198467 q = 1) : d201672 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17473, d201672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17473, d201672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17474 q = 1) (hb : d198467 q = 1) : d201673 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17474, d201673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17474, d201673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17475 q = 1) (hb : d198467 q = 1) : d201674 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17475, d201674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17475, d201674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d17476 q = 1) (hb : d198467 q = 1) : d201675 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17476, d201675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17476, d201675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17477 q = 1) (hb : d198467 q = 1) : d201676 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17477, d201676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17477, d201676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro53638 (p : Pattern) (ha : d17483 p = 1) (hb : d198467 p = 1) : d201682 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17478 q = 1) (hb : d198467 q = 1) : d201677 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17478, d201677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53637 q ha hb
    | true =>
      simp only [d17478, d201677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17479 q = 1) (hb : d198467 q = 1) : d201678 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17479, d201678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17479, d201678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17480 q = 1) (hb : d198467 q = 1) : d201679 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17480, d201679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17480, d201679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17481 q = 1) (hb : d198467 q = 1) : d201680 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17481, d201680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17481, d201680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17482 q = 1) (hb : d198467 q = 1) : d201681 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17482, d201681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17482, d201681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17483 q = 1) (hb : d198467 q = 1) : d201682 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17483, d201682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17483, d201682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53639 (p : Pattern) (ha : d128422 p = 1) (hb : d198467 p = 1) : d201688 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17429 q = 1) (hb : d198467 q = 1) : d201668 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17429, d201668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53634 q ha hb
    | true =>
      simp only [d17429, d201668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53635 q ha hb
  have h2 (q : Pattern) (ha : d128418 q = 1) (hb : d198467 q = 1) : d201669 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128418, d201669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128418, d201669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17484 q = 1) (hb : d198467 q = 1) : d201683 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17484, d201683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53638 q ha hb
    | true =>
      simp only [d17484, d201683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17485 q = 1) (hb : d198467 q = 1) : d201684 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17485, d201684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17485, d201684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128419 q = 1) (hb : d198467 q = 1) : d201685 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128419, d201685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128419, d201685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128420 q = 1) (hb : d198467 q = 1) : d201686 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128420, d201686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128420, d201686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128421 q = 1) (hb : d198467 q = 1) : d201687 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128421, d201687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128421, d201687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128422 q = 1) (hb : d198467 q = 1) : d201688 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128422, d201688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128422, d201688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53640 (p : Pattern) (ha : d128428 p = 1) (hb : d198467 p = 1) : d201705 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17195 q = 1) (hb : d198467 q = 1) : d201510 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17195, d201510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17195, d201510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53592 q ha hb
  have h2 (q : Pattern) (ha : d17196 q = 1) (hb : d198467 q = 1) : d201511 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d17196, d201511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17196, d201511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17205 q = 1) (hb : d198467 q = 1) : d201520 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17205, d201520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53592 q ha hb
    | true =>
      simp only [d17205, d201520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53595 q ha hb
  have h4 (q : Pattern) (ha : d17206 q = 1) (hb : d198467 q = 1) : d201521 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d17206, d201521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17206, d201521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17207 q = 1) (hb : d198467 q = 1) : d201522 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d17207, d201522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17207, d201522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128406 q = 1) (hb : d198467 q = 1) : d201597 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128406, d201597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53618 q ha hb
    | true =>
      simp only [d128406, d201597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53626 q ha hb
  have h7 (q : Pattern) (ha : d17355 q = 1) (hb : d198467 q = 1) : d201610 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17355, d201610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53598 q ha hb
    | true =>
      simp only [d17355, d201610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53599 q ha hb
  have h8 (q : Pattern) (ha : d128407 q = 1) (hb : d198467 q = 1) : d201611 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128407, d201611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128407, d201611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128408 q = 1) (hb : d198467 q = 1) : d201612 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128408, d201612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128408, d201612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d128409 q = 1) (hb : d198467 q = 1) : d201613 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128409, d201613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128409, d201613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128413 q = 1) (hb : d198467 q = 1) : d201617 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128413, d201617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128413, d201617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53627 q ha hb
  have h12 (q : Pattern) (ha : d17364 q = 1) (hb : d198467 q = 1) : d201619 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17364, d201619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17364, d201619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53600 q ha hb
  have h13 (q : Pattern) (ha : d128414 q = 1) (hb : d198467 q = 1) : d201620 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128414, d201620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128414, d201620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128415 q = 1) (hb : d198467 q = 1) : d201621 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128415, d201621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128415, d201621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d128416 q = 1) (hb : d198467 q = 1) : d201622 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128416, d201622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128416, d201622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d128417 q = 1) (hb : d198467 q = 1) : d201623 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128417, d201623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128417, d201623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d128423 q = 1) (hb : d198467 q = 1) : d201689 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128423, d201689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128423, d201689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53639 q ha hb
  have h18 (q : Pattern) (ha : d17501 q = 1) (hb : d198467 q = 1) : d201700 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17501, d201700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17501, d201700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53605 q ha hb
  have h19 (q : Pattern) (ha : d128424 q = 1) (hb : d198467 q = 1) : d201701 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128424, d201701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128424, d201701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d128425 q = 1) (hb : d198467 q = 1) : d201702 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128425, d201702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d128425, d201702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d128426 q = 1) (hb : d198467 q = 1) : d201703 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128426, d201703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d128426, d201703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d128427 q = 1) (hb : d198467 q = 1) : d201704 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128427, d201704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128427, d201704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d128428 q = 1) (hb : d198467 q = 1) : d201705 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128428, d201705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128428, d201705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro53641 (p : Pattern) (ha : d128434 p = 1) (hb : d198467 p = 1) : d201711 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128429 q = 1) (hb : d198467 q = 1) : d201706 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128429, d201706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128429, d201706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53640 q ha hb
  have h2 (q : Pattern) (ha : d128430 q = 1) (hb : d198467 q = 1) : d201707 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128430, d201707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128430, d201707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128431 q = 1) (hb : d198467 q = 1) : d201708 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128431, d201708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128431, d201708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128432 q = 1) (hb : d198467 q = 1) : d201709 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128432, d201709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128432, d201709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128433 q = 1) (hb : d198467 q = 1) : d201710 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128433, d201710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128433, d201710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128434 q = 1) (hb : d198467 q = 1) : d201711 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128434, d201711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128434, d201711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53642 (p : Pattern) (ha : d128440 p = 1) (hb : d198467 p = 1) : d201717 p = 1 := by
  have h0 (q : Pattern) (ha : d128269 q = 1) (hb : d198467 q = 1) : d200681 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128269, d200681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53348 q ha hb
    | true =>
      simp only [d128269, d200681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53393 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d128309 q = 1) (hb : d198467 q = 1) : d200919 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128309, d200919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128309, d200919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53442 q ha hb
  have h3 (q : Pattern) (ha : d128310 q = 1) (hb : d198467 q = 1) : d200920 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128310, d200920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128310, d200920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128350 q = 1) (hb : d198467 q = 1) : d201202 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128350, d201202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128350, d201202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53510 q ha hb
  have h5 (q : Pattern) (ha : d128351 q = 1) (hb : d198467 q = 1) : d201203 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128351, d201203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128351, d201203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128352 q = 1) (hb : d198467 q = 1) : d201204 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d128352, d201204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128352, d201204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128392 q = 1) (hb : d198467 q = 1) : d201466 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128392, d201466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128392, d201466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53577 q ha hb
  have h8 (q : Pattern) (ha : d128393 q = 1) (hb : d198467 q = 1) : d201467 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128393, d201467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128393, d201467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128394 q = 1) (hb : d198467 q = 1) : d201468 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d128394, d201468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128394, d201468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128395 q = 1) (hb : d198467 q = 1) : d201469 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d128395, d201469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128395, d201469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128435 q = 1) (hb : d198467 q = 1) : d201712 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128435, d201712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128435, d201712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53641 q ha hb
  have h12 (q : Pattern) (ha : d128436 q = 1) (hb : d198467 q = 1) : d201713 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128436, d201713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128436, d201713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128437 q = 1) (hb : d198467 q = 1) : d201714 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d128437, d201714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128437, d201714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128438 q = 1) (hb : d198467 q = 1) : d201715 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d128438, d201715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128438, d201715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128439 q = 1) (hb : d198467 q = 1) : d201716 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d128439, d201716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128439, d201716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d128440 q = 1) (hb : d198467 q = 1) : d201717 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d128440, d201717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128440, d201717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro53643 (p : Pattern) (ha : d128446 p = 1) (hb : d198467 p = 1) : d201723 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128441 q = 1) (hb : d198467 q = 1) : d201718 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d128441, d201718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53642 q ha hb
    | true =>
      simp only [d128441, d201718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128442 q = 1) (hb : d198467 q = 1) : d201719 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d128442, d201719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128442, d201719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128443 q = 1) (hb : d198467 q = 1) : d201720 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d128443, d201720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128443, d201720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128444 q = 1) (hb : d198467 q = 1) : d201721 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d128444, d201721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128444, d201721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128445 q = 1) (hb : d198467 q = 1) : d201722 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d128445, d201722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128445, d201722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128446 q = 1) (hb : d198467 q = 1) : d201723 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d128446, d201723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128446, d201723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53644 (p : Pattern) (ha : d128452 p = 1) (hb : d198467 p = 1) : d201729 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128447 q = 1) (hb : d198467 q = 1) : d201724 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d128447, d201724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53643 q ha hb
    | true =>
      simp only [d128447, d201724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128448 q = 1) (hb : d198467 q = 1) : d201725 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d128448, d201725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128448, d201725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128449 q = 1) (hb : d198467 q = 1) : d201726 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d128449, d201726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128449, d201726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128450 q = 1) (hb : d198467 q = 1) : d201727 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d128450, d201727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128450, d201727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128451 q = 1) (hb : d198467 q = 1) : d201728 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d128451, d201728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128451, d201728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128452 q = 1) (hb : d198467 q = 1) : d201729 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d128452, d201729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128452, d201729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53645 (p : Pattern) (ha : d128458 p = 1) (hb : d212559 p = 1) : d201735 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128453 q = 1) (hb : d198467 q = 1) : d201730 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d128453, d201730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53644 q ha hb
    | true =>
      simp only [d128453, d201730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128454 q = 1) (hb : d198467 q = 1) : d201731 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d128454, d201731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128454, d201731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128455 q = 1) (hb : d198467 q = 1) : d201732 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d128455, d201732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128455, d201732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128456 q = 1) (hb : d198467 q = 1) : d201733 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d128456, d201733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128456, d201733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128457 q = 1) (hb : d198467 q = 1) : d201734 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d128457, d201734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128457, d201734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d128458 q = 1) (hb : d212559 q = 1) : d201735 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d128458, d212559, d201735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128458, d212559, d201735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro53646 (p : Pattern) (ha : d128464 p = 1) (hb : d212559 p = 1) : d201741 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d212559 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128459 q = 1) (hb : d212559 q = 1) : d201736 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d128459, d201736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53645 q ha hb
    | true =>
      simp only [d128459, d201736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128460 q = 1) (hb : d212559 q = 1) : d201737 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d128460, d201737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128460, d201737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128461 q = 1) (hb : d212559 q = 1) : d201738 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d128461, d201738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128461, d201738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128462 q = 1) (hb : d212559 q = 1) : d201739 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d128462, d201739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128462, d201739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128463 q = 1) (hb : d212559 q = 1) : d201740 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d128463, d201740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128463, d201740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128464 q = 1) (hb : d212559 q = 1) : d201741 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d128464, d201741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128464, d201741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53647 (p : Pattern) (ha : d128470 p = 1) (hb : d212559 p = 1) : d201747 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d212559 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128465 q = 1) (hb : d212559 q = 1) : d201742 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d128465, d201742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53646 q ha hb
    | true =>
      simp only [d128465, d201742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128466 q = 1) (hb : d212559 q = 1) : d201743 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d128466, d201743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128466, d201743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128467 q = 1) (hb : d212559 q = 1) : d201744 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d128467, d201744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128467, d201744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128468 q = 1) (hb : d212559 q = 1) : d201745 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d128468, d201745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128468, d201745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128469 q = 1) (hb : d212559 q = 1) : d201746 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d128469, d201746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128469, d201746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128470 q = 1) (hb : d212559 q = 1) : d201747 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d128470, d201747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128470, d201747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53648 (p : Pattern) (ha : d128476 p = 1) (hb : d212559 p = 1) : d201753 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d212559 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128471 q = 1) (hb : d212559 q = 1) : d201748 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d128471, d201748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53647 q ha hb
    | true =>
      simp only [d128471, d201748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128472 q = 1) (hb : d212559 q = 1) : d201749 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d128472, d201749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128472, d201749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128473 q = 1) (hb : d212559 q = 1) : d201750 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d128473, d201750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128473, d201750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128474 q = 1) (hb : d212559 q = 1) : d201751 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d128474, d201751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128474, d201751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128475 q = 1) (hb : d212559 q = 1) : d201752 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d128475, d201752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128475, d201752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128476 q = 1) (hb : d212559 q = 1) : d201753 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d128476, d201753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128476, d201753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53649 (p : Pattern) (ha : d128482 p = 1) (hb : d212559 p = 1) : d201759 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d212559 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128477 q = 1) (hb : d212559 q = 1) : d201754 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d128477, d201754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53648 q ha hb
    | true =>
      simp only [d128477, d201754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128478 q = 1) (hb : d212559 q = 1) : d201755 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d128478, d201755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128478, d201755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128479 q = 1) (hb : d212559 q = 1) : d201756 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d128479, d201756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128479, d201756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128480 q = 1) (hb : d212559 q = 1) : d201757 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d128480, d201757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128480, d201757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128481 q = 1) (hb : d212559 q = 1) : d201758 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d128481, d201758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128481, d201758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128482 q = 1) (hb : d212559 q = 1) : d201759 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d128482, d201759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128482, d201759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53650 (p : Pattern) (ha : d53655 p = 1) (hb : d198467 p = 1) : d201762 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d198467 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d204 q = 1) (hb : d198467 q = 1) : d200271 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d200271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53314 q ha hb
    | true =>
      simp only [d204, d200271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d287 q = 1) (hb : d198467 q = 1) : d200327 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, d200327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287, d200327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d288 q = 1) (hb : d198467 q = 1) : d200328 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, d200328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288, d200328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d289 q = 1) (hb : d198467 q = 1) : d200329 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, d200329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289, d200329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d290 q = 1) (hb : d198467 q = 1) : d200330 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, d200330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, d200330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53655 q = 1) (hb : d198467 q = 1) : d201762 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53655, d201762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53655, d201762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro53651 (p : Pattern) (ha : d53665 p = 1) (hb : d198467 p = 1) : d201772 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d198467 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d244 q = 1) (hb : d198467 q = 1) : d200303 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d244, d200303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53318 q ha hb
    | true =>
      simp only [d244, d200303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53661 q = 1) (hb : d198467 q = 1) : d201768 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53661, d201768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53661, d201768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53662 q = 1) (hb : d198467 q = 1) : d201769 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53662, d201769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53662, d201769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53663 q = 1) (hb : d198467 q = 1) : d201770 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53663, d201770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53663, d201770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53664 q = 1) (hb : d198467 q = 1) : d201771 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53664, d201771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53664, d201771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53665 q = 1) (hb : d198467 q = 1) : d201772 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53665, d201772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53665, d201772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro53652 (p : Pattern) (ha : d53671 p = 1) (hb : d198467 p = 1) : d201778 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292 q = 1) (hb : d198467 q = 1) : d200332 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d200332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53324 q ha hb
    | true =>
      simp only [d292, d200332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53325 q ha hb
  have h2 (q : Pattern) (ha : d293 q = 1) (hb : d198467 q = 1) : d200333 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d200333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293, d200333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53653 q = 1) (hb : d198467 q = 1) : d201760 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53653, d201760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53653, d201760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53654 q = 1) (hb : d198467 q = 1) : d201761 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53654, d201761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53654, d201761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53656 q = 1) (hb : d198467 q = 1) : d201763 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53656, d201763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53656, d201763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53650 q ha hb
  have h6 (q : Pattern) (ha : d53657 q = 1) (hb : d198467 q = 1) : d201764 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53657, d201764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53657, d201764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53658 q = 1) (hb : d198467 q = 1) : d201765 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53658, d201765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53658, d201765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53659 q = 1) (hb : d198467 q = 1) : d201766 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53659, d201766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53659, d201766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53660 q = 1) (hb : d198467 q = 1) : d201767 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53660, d201767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53660, d201767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53666 q = 1) (hb : d198467 q = 1) : d201773 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53666, d201773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53666, d201773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53651 q ha hb
  have h11 (q : Pattern) (ha : d53667 q = 1) (hb : d198467 q = 1) : d201774 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53667, d201774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53667, d201774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53668 q = 1) (hb : d198467 q = 1) : d201775 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53668, d201775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53668, d201775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53669 q = 1) (hb : d198467 q = 1) : d201776 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53669, d201776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53669, d201776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53670 q = 1) (hb : d198467 q = 1) : d201777 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53670, d201777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53670, d201777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53671 q = 1) (hb : d198467 q = 1) : d201778 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53671, d201778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53671, d201778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro53653 (p : Pattern) (ha : d53677 p = 1) (hb : d198467 p = 1) : d201784 p = 1 := by
  have h0 (q : Pattern) (ha : d53652 q = 1) (hb : d198467 q = 1) : d53652 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53672 q = 1) (hb : d198467 q = 1) : d201779 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53672, d201779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53672, d201779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53652 q ha hb
  have h3 (q : Pattern) (ha : d53673 q = 1) (hb : d198467 q = 1) : d201780 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53673, d201780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53673, d201780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53674 q = 1) (hb : d198467 q = 1) : d201781 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53674, d201781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53674, d201781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53675 q = 1) (hb : d198467 q = 1) : d201782 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53675, d201782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53675, d201782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53676 q = 1) (hb : d198467 q = 1) : d201783 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53676, d201783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53676, d201783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53677 q = 1) (hb : d198467 q = 1) : d201784 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53677, d201784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53677, d201784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro53654 (p : Pattern) (ha : d171078 p = 1) (hb : d198467 p = 1) : d201787 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16052 q = 1) (hb : d198467 q = 1) : d200491 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16052, d200491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53360 q ha hb
    | true =>
      simp only [d16052, d200491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53351 q ha hb
  have h2 (q : Pattern) (ha : d16053 q = 1) (hb : d198467 q = 1) : d200492 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16053, d200492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16053, d200492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16054 q = 1) (hb : d198467 q = 1) : d200493 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16054, d200493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16054, d200493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16055 q = 1) (hb : d198467 q = 1) : d200494 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16055, d200494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16055, d200494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16056 q = 1) (hb : d198467 q = 1) : d200495 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16056, d200495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16056, d200495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171078 q = 1) (hb : d198467 q = 1) : d201787 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171078, d201787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171078, d201787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53655 (p : Pattern) (ha : d171089 p = 1) (hb : d198467 p = 1) : d201798 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171084 q = 1) (hb : d198467 q = 1) : d201793 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d171084, d201793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53389 q ha hb
    | true =>
      simp only [d171084, d201793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53355 q ha hb
  have h2 (q : Pattern) (ha : d171085 q = 1) (hb : d198467 q = 1) : d201794 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d171085, d201794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171085, d201794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d171086 q = 1) (hb : d198467 q = 1) : d201795 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d171086, d201795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171086, d201795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171087 q = 1) (hb : d198467 q = 1) : d201796 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d171087, d201796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171087, d201796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171088 q = 1) (hb : d198467 q = 1) : d201797 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d171088, d201797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171088, d201797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171089 q = 1) (hb : d198467 q = 1) : d201798 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171089, d201798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171089, d201798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53656 (p : Pattern) (ha : d171095 p = 1) (hb : d198467 p = 1) : d201804 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16058 q = 1) (hb : d198467 q = 1) : d200497 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16058, d200497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53359 q ha hb
    | true =>
      simp only [d16058, d200497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53361 q ha hb
  have h2 (q : Pattern) (ha : d16059 q = 1) (hb : d198467 q = 1) : d200498 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16059, d200498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16059, d200498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d171076 q = 1) (hb : d198467 q = 1) : d201785 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171076, d201785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171076, d201785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171077 q = 1) (hb : d198467 q = 1) : d201786 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171077, d201786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171077, d201786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171079 q = 1) (hb : d198467 q = 1) : d201788 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171079, d201788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171079, d201788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53654 q ha hb
  have h6 (q : Pattern) (ha : d171080 q = 1) (hb : d198467 q = 1) : d201789 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171080, d201789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171080, d201789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d171081 q = 1) (hb : d198467 q = 1) : d201790 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171081, d201790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171081, d201790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d171082 q = 1) (hb : d198467 q = 1) : d201791 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171082, d201791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171082, d201791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d171083 q = 1) (hb : d198467 q = 1) : d201792 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171083, d201792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171083, d201792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d171090 q = 1) (hb : d198467 q = 1) : d201799 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171090, d201799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171090, d201799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53655 q ha hb
  have h11 (q : Pattern) (ha : d171091 q = 1) (hb : d198467 q = 1) : d201800 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171091, d201800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d171091, d201800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d171092 q = 1) (hb : d198467 q = 1) : d201801 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171092, d201801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d171092, d201801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d171093 q = 1) (hb : d198467 q = 1) : d201802 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171093, d201802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171093, d201802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d171094 q = 1) (hb : d198467 q = 1) : d201803 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171094, d201803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d171094, d201803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d171095 q = 1) (hb : d198467 q = 1) : d201804 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d171095, d201804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d171095, d201804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro53657 (p : Pattern) (ha : d171101 p = 1) (hb : d198467 p = 1) : d201810 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171096 q = 1) (hb : d198467 q = 1) : d201805 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d171096, d201805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171096, d201805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53656 q ha hb
  have h2 (q : Pattern) (ha : d171097 q = 1) (hb : d198467 q = 1) : d201806 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d171097, d201806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171097, d201806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d171098 q = 1) (hb : d198467 q = 1) : d201807 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d171098, d201807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171098, d201807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d171099 q = 1) (hb : d198467 q = 1) : d201808 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d171099, d201808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171099, d201808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171100 q = 1) (hb : d198467 q = 1) : d201809 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d171100, d201809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171100, d201809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171101 q = 1) (hb : d198467 q = 1) : d201810 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d171101, d201810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171101, d201810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53658 (p : Pattern) (ha : d171105 p = 1) (hb : d198467 p = 1) : d201814 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16249 q = 1) (hb : d198467 q = 1) : d200719 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16249, d200719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53408 q ha hb
    | true =>
      simp only [d16249, d200719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53397 q ha hb
  have h2 (q : Pattern) (ha : d16250 q = 1) (hb : d198467 q = 1) : d200720 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16250, d200720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16250, d200720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16251 q = 1) (hb : d198467 q = 1) : d200721 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16251, d200721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16251, d200721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16252 q = 1) (hb : d198467 q = 1) : d200722 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16252, d200722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16252, d200722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16253 q = 1) (hb : d198467 q = 1) : d200723 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16253, d200723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16253, d200723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171105 q = 1) (hb : d198467 q = 1) : d201814 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171105, d201814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171105, d201814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53659 (p : Pattern) (ha : d171116 p = 1) (hb : d198467 p = 1) : d201825 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171111 q = 1) (hb : d198467 q = 1) : d201820 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d171111, d201820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53438 q ha hb
    | true =>
      simp only [d171111, d201820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53402 q ha hb
  have h2 (q : Pattern) (ha : d171112 q = 1) (hb : d198467 q = 1) : d201821 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d171112, d201821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171112, d201821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d171113 q = 1) (hb : d198467 q = 1) : d201822 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d171113, d201822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171113, d201822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171114 q = 1) (hb : d198467 q = 1) : d201823 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d171114, d201823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171114, d201823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171115 q = 1) (hb : d198467 q = 1) : d201824 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d171115, d201824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171115, d201824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171116 q = 1) (hb : d198467 q = 1) : d201825 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171116, d201825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171116, d201825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53660 (p : Pattern) (ha : d171122 p = 1) (hb : d198467 p = 1) : d201831 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16255 q = 1) (hb : d198467 q = 1) : d200725 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16255, d200725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53407 q ha hb
    | true =>
      simp only [d16255, d200725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53409 q ha hb
  have h2 (q : Pattern) (ha : d16256 q = 1) (hb : d198467 q = 1) : d200726 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16256, d200726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16256, d200726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d171103 q = 1) (hb : d198467 q = 1) : d201812 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171103, d201812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171103, d201812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171104 q = 1) (hb : d198467 q = 1) : d201813 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171104, d201813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171104, d201813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171106 q = 1) (hb : d198467 q = 1) : d201815 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171106, d201815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171106, d201815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53658 q ha hb
  have h6 (q : Pattern) (ha : d171107 q = 1) (hb : d198467 q = 1) : d201816 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171107, d201816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171107, d201816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d171108 q = 1) (hb : d198467 q = 1) : d201817 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171108, d201817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171108, d201817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d171109 q = 1) (hb : d198467 q = 1) : d201818 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171109, d201818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171109, d201818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d171110 q = 1) (hb : d198467 q = 1) : d201819 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171110, d201819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171110, d201819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d171117 q = 1) (hb : d198467 q = 1) : d201826 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171117, d201826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171117, d201826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53659 q ha hb
  have h11 (q : Pattern) (ha : d171118 q = 1) (hb : d198467 q = 1) : d201827 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171118, d201827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d171118, d201827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d171119 q = 1) (hb : d198467 q = 1) : d201828 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171119, d201828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d171119, d201828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d171120 q = 1) (hb : d198467 q = 1) : d201829 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171120, d201829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171120, d201829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d171121 q = 1) (hb : d198467 q = 1) : d201830 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171121, d201830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d171121, d201830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d171122 q = 1) (hb : d198467 q = 1) : d201831 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d171122, d201831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d171122, d201831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro53661 (p : Pattern) (ha : d171128 p = 1) (hb : d198467 p = 1) : d201837 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171123 q = 1) (hb : d198467 q = 1) : d201832 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d171123, d201832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171123, d201832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53660 q ha hb
  have h2 (q : Pattern) (ha : d171124 q = 1) (hb : d198467 q = 1) : d201833 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d171124, d201833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171124, d201833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d171125 q = 1) (hb : d198467 q = 1) : d201834 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d171125, d201834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171125, d201834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d171126 q = 1) (hb : d198467 q = 1) : d201835 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d171126, d201835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171126, d201835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171127 q = 1) (hb : d198467 q = 1) : d201836 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d171127, d201836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171127, d201836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171128 q = 1) (hb : d198467 q = 1) : d201837 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d171128, d201837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171128, d201837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53662 (p : Pattern) (ha : d171133 p = 1) (hb : d198467 p = 1) : d201842 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16481 q = 1) (hb : d198467 q = 1) : d200977 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16481, d200977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53459 q ha hb
    | true =>
      simp only [d16481, d200977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53460 q ha hb
  have h2 (q : Pattern) (ha : d16482 q = 1) (hb : d198467 q = 1) : d200978 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16482, d200978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16482, d200978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16483 q = 1) (hb : d198467 q = 1) : d200979 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16483, d200979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16483, d200979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16484 q = 1) (hb : d198467 q = 1) : d200980 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16484, d200980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16484, d200980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16485 q = 1) (hb : d198467 q = 1) : d200981 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16485, d200981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16485, d200981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171133 q = 1) (hb : d198467 q = 1) : d201842 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171133, d201842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171133, d201842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53663 (p : Pattern) (ha : d171140 p = 1) (hb : d198467 p = 1) : d201143 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16673 q = 1) (hb : d198467 q = 1) : d201129 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16673, d201129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53499 q ha hb
    | true =>
      simp only [d16673, d201129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53468 q ha hb
  have h2 (q : Pattern) (ha : d16674 q = 1) (hb : d198467 q = 1) : d201130 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16674, d201130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16674, d201130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16675 q = 1) (hb : d198467 q = 1) : d201131 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16675, d201131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16675, d201131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16676 q = 1) (hb : d198467 q = 1) : d201133 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16676, d201133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53468 q ha hb
    | true =>
      simp only [d16676, d201133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53497 q ha hb
  have h5 (q : Pattern) (ha : d16677 q = 1) (hb : d198467 q = 1) : d201134 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16677, d201134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16677, d201134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16678 q = 1) (hb : d198467 q = 1) : d201135 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16678, d201135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16678, d201135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16679 q = 1) (hb : d198467 q = 1) : d201136 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16679, d201136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16679, d201136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16693 q = 1) (hb : d198467 q = 1) : d201133 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16693, d201133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53468 q ha hb
    | true =>
      simp only [d16693, d201133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53467 q ha hb
  have h9 (q : Pattern) (ha : d16694 q = 1) (hb : d198467 q = 1) : d201134 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16694, d201134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16694, d201134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16695 q = 1) (hb : d198467 q = 1) : d201135 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16695, d201135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16695, d201135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16696 q = 1) (hb : d198467 q = 1) : d201141 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16696, d201141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16696, d201141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d171139 q = 1) (hb : d198467 q = 1) : d201142 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d171139, d201142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171139, d201142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d171140 q = 1) (hb : d198467 q = 1) : d201143 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d171140, d201143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171140, d201143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro53664 (p : Pattern) (ha : d171146 p = 1) (hb : d198467 p = 1) : d201157 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171141 q = 1) (hb : d198467 q = 1) : d201144 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d171141, d201144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53663 q ha hb
    | true =>
      simp only [d171141, d201144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d171142 q = 1) (hb : d198467 q = 1) : d201145 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d171142, d201145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171142, d201145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16699 q = 1) (hb : d198467 q = 1) : d201152 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16699, d201152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53469 q ha hb
    | true =>
      simp only [d16699, d201152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16700 q = 1) (hb : d198467 q = 1) : d201153 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16700, d201153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16700, d201153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171143 q = 1) (hb : d198467 q = 1) : d201154 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d171143, d201154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171143, d201154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171144 q = 1) (hb : d198467 q = 1) : d201155 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d171144, d201155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171144, d201155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d171145 q = 1) (hb : d198467 q = 1) : d201156 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d171145, d201156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171145, d201156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d171146 q = 1) (hb : d198467 q = 1) : d201157 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d171146, d201157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171146, d201157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro53665 (p : Pattern) (ha : d171152 p = 1) (hb : d198467 p = 1) : d201853 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171147 q = 1) (hb : d198467 q = 1) : d201848 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d171147, d201848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53664 q ha hb
    | true =>
      simp only [d171147, d201848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53470 q ha hb
  have h2 (q : Pattern) (ha : d171148 q = 1) (hb : d198467 q = 1) : d201849 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d171148, d201849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171148, d201849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d171149 q = 1) (hb : d198467 q = 1) : d201850 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d171149, d201850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171149, d201850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171150 q = 1) (hb : d198467 q = 1) : d201851 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d171150, d201851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171150, d201851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171151 q = 1) (hb : d198467 q = 1) : d201852 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d171151, d201852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171151, d201852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171152 q = 1) (hb : d198467 q = 1) : d201853 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171152, d201853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171152, d201853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53666 (p : Pattern) (ha : d171158 p = 1) (hb : d198467 p = 1) : d201859 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16487 q = 1) (hb : d198467 q = 1) : d200983 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16487, d200983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53458 q ha hb
    | true =>
      simp only [d16487, d200983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53461 q ha hb
  have h2 (q : Pattern) (ha : d16488 q = 1) (hb : d198467 q = 1) : d200984 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16488, d200984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16488, d200984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d171131 q = 1) (hb : d198467 q = 1) : d201840 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171131, d201840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171131, d201840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171132 q = 1) (hb : d198467 q = 1) : d201841 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171132, d201841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171132, d201841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171134 q = 1) (hb : d198467 q = 1) : d201843 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171134, d201843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171134, d201843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53662 q ha hb
  have h6 (q : Pattern) (ha : d171135 q = 1) (hb : d198467 q = 1) : d201844 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171135, d201844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171135, d201844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d171136 q = 1) (hb : d198467 q = 1) : d201845 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171136, d201845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171136, d201845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d171137 q = 1) (hb : d198467 q = 1) : d201846 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171137, d201846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171137, d201846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d171138 q = 1) (hb : d198467 q = 1) : d201847 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171138, d201847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171138, d201847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d171153 q = 1) (hb : d198467 q = 1) : d201854 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171153, d201854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171153, d201854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53665 q ha hb
  have h11 (q : Pattern) (ha : d171154 q = 1) (hb : d198467 q = 1) : d201855 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171154, d201855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d171154, d201855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d171155 q = 1) (hb : d198467 q = 1) : d201856 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171155, d201856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d171155, d201856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d171156 q = 1) (hb : d198467 q = 1) : d201857 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171156, d201857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171156, d201857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d171157 q = 1) (hb : d198467 q = 1) : d201858 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171157, d201858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d171157, d201858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d171158 q = 1) (hb : d198467 q = 1) : d201859 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d171158, d201859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d171158, d201859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro53667 (p : Pattern) (ha : d171164 p = 1) (hb : d198467 p = 1) : d201865 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171159 q = 1) (hb : d198467 q = 1) : d201860 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d171159, d201860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171159, d201860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53666 q ha hb
  have h2 (q : Pattern) (ha : d171160 q = 1) (hb : d198467 q = 1) : d201861 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d171160, d201861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171160, d201861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d171161 q = 1) (hb : d198467 q = 1) : d201862 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d171161, d201862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171161, d201862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d171162 q = 1) (hb : d198467 q = 1) : d201863 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d171162, d201863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171162, d201863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171163 q = 1) (hb : d198467 q = 1) : d201864 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d171163, d201864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171163, d201864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171164 q = 1) (hb : d198467 q = 1) : d201865 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d171164, d201865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171164, d201865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53668 (p : Pattern) (ha : d171170 p = 1) (hb : d198467 p = 1) : d201871 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16833 q = 1) (hb : d198467 q = 1) : d201256 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16833, d201256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53528 q ha hb
    | true =>
      simp only [d16833, d201256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53529 q ha hb
  have h2 (q : Pattern) (ha : d16834 q = 1) (hb : d198467 q = 1) : d201257 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16834, d201257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16834, d201257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16835 q = 1) (hb : d198467 q = 1) : d201258 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16835, d201258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16835, d201258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16836 q = 1) (hb : d198467 q = 1) : d201259 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16836, d201259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16836, d201259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16837 q = 1) (hb : d198467 q = 1) : d201260 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16837, d201260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16837, d201260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171170 q = 1) (hb : d198467 q = 1) : d201871 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171170, d201871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171170, d201871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53669 (p : Pattern) (ha : d171177 p = 1) (hb : d198467 p = 1) : d201407 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17033 q = 1) (hb : d198467 q = 1) : d201393 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17033, d201393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53566 q ha hb
    | true =>
      simp only [d17033, d201393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53537 q ha hb
  have h2 (q : Pattern) (ha : d17034 q = 1) (hb : d198467 q = 1) : d201394 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17034, d201394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17034, d201394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17035 q = 1) (hb : d198467 q = 1) : d201395 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17035, d201395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17035, d201395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17036 q = 1) (hb : d198467 q = 1) : d201397 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17036, d201397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53537 q ha hb
    | true =>
      simp only [d17036, d201397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53564 q ha hb
  have h5 (q : Pattern) (ha : d17037 q = 1) (hb : d198467 q = 1) : d201398 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17037, d201398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17037, d201398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17038 q = 1) (hb : d198467 q = 1) : d201399 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17038, d201399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17038, d201399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17039 q = 1) (hb : d198467 q = 1) : d201400 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17039, d201400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17039, d201400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17053 q = 1) (hb : d198467 q = 1) : d201397 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17053, d201397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53537 q ha hb
    | true =>
      simp only [d17053, d201397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53536 q ha hb
  have h9 (q : Pattern) (ha : d17054 q = 1) (hb : d198467 q = 1) : d201398 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17054, d201398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17054, d201398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17055 q = 1) (hb : d198467 q = 1) : d201399 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17055, d201399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17055, d201399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17056 q = 1) (hb : d198467 q = 1) : d201405 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17056, d201405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17056, d201405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d171176 q = 1) (hb : d198467 q = 1) : d201406 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d171176, d201406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171176, d201406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d171177 q = 1) (hb : d198467 q = 1) : d201407 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d171177, d201407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171177, d201407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro53670 (p : Pattern) (ha : d171183 p = 1) (hb : d198467 p = 1) : d201421 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171178 q = 1) (hb : d198467 q = 1) : d201408 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d171178, d201408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53669 q ha hb
    | true =>
      simp only [d171178, d201408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d171179 q = 1) (hb : d198467 q = 1) : d201409 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d171179, d201409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171179, d201409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17059 q = 1) (hb : d198467 q = 1) : d201416 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17059, d201416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53538 q ha hb
    | true =>
      simp only [d17059, d201416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17060 q = 1) (hb : d198467 q = 1) : d201417 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17060, d201417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17060, d201417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171180 q = 1) (hb : d198467 q = 1) : d201418 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d171180, d201418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171180, d201418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171181 q = 1) (hb : d198467 q = 1) : d201419 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d171181, d201419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171181, d201419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d171182 q = 1) (hb : d198467 q = 1) : d201420 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d171182, d201420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171182, d201420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d171183 q = 1) (hb : d198467 q = 1) : d201421 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d171183, d201421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171183, d201421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro53671 (p : Pattern) (ha : d171189 p = 1) (hb : d198467 p = 1) : d201882 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171184 q = 1) (hb : d198467 q = 1) : d201877 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d171184, d201877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53670 q ha hb
    | true =>
      simp only [d171184, d201877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53539 q ha hb
  have h2 (q : Pattern) (ha : d171185 q = 1) (hb : d198467 q = 1) : d201878 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d171185, d201878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171185, d201878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d171186 q = 1) (hb : d198467 q = 1) : d201879 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d171186, d201879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171186, d201879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171187 q = 1) (hb : d198467 q = 1) : d201880 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d171187, d201880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171187, d201880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171188 q = 1) (hb : d198467 q = 1) : d201881 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d171188, d201881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171188, d201881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171189 q = 1) (hb : d198467 q = 1) : d201882 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171189, d201882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171189, d201882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53672 (p : Pattern) (ha : d171195 p = 1) (hb : d198467 p = 1) : d201888 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16839 q = 1) (hb : d198467 q = 1) : d201262 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16839, d201262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53527 q ha hb
    | true =>
      simp only [d16839, d201262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53530 q ha hb
  have h2 (q : Pattern) (ha : d16840 q = 1) (hb : d198467 q = 1) : d201263 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16840, d201263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16840, d201263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d171168 q = 1) (hb : d198467 q = 1) : d201869 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171168, d201869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171168, d201869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171169 q = 1) (hb : d198467 q = 1) : d201870 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171169, d201870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171169, d201870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171171 q = 1) (hb : d198467 q = 1) : d201872 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171171, d201872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171171, d201872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53668 q ha hb
  have h6 (q : Pattern) (ha : d171172 q = 1) (hb : d198467 q = 1) : d201873 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171172, d201873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171172, d201873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d171173 q = 1) (hb : d198467 q = 1) : d201874 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171173, d201874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171173, d201874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d171174 q = 1) (hb : d198467 q = 1) : d201875 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171174, d201875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171174, d201875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d171175 q = 1) (hb : d198467 q = 1) : d201876 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171175, d201876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171175, d201876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d171190 q = 1) (hb : d198467 q = 1) : d201883 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171190, d201883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171190, d201883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53671 q ha hb
  have h11 (q : Pattern) (ha : d171191 q = 1) (hb : d198467 q = 1) : d201884 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171191, d201884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d171191, d201884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d171192 q = 1) (hb : d198467 q = 1) : d201885 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171192, d201885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d171192, d201885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d171193 q = 1) (hb : d198467 q = 1) : d201886 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171193, d201886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171193, d201886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d171194 q = 1) (hb : d198467 q = 1) : d201887 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171194, d201887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d171194, d201887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d171195 q = 1) (hb : d198467 q = 1) : d201888 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d171195, d201888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d171195, d201888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro53673 (p : Pattern) (ha : d171201 p = 1) (hb : d198467 p = 1) : d201894 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171196 q = 1) (hb : d198467 q = 1) : d201889 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d171196, d201889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171196, d201889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53672 q ha hb
  have h2 (q : Pattern) (ha : d171197 q = 1) (hb : d198467 q = 1) : d201890 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d171197, d201890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171197, d201890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d171198 q = 1) (hb : d198467 q = 1) : d201891 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d171198, d201891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171198, d201891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d171199 q = 1) (hb : d198467 q = 1) : d201892 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d171199, d201892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171199, d201892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171200 q = 1) (hb : d198467 q = 1) : d201893 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d171200, d201893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171200, d201893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171201 q = 1) (hb : d198467 q = 1) : d201894 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d171201, d201894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171201, d201894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53674 (p : Pattern) (ha : d171208 p = 1) (hb : d198467 p = 1) : d201901 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17199 q = 1) (hb : d198467 q = 1) : d201514 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17199, d201514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53593 q ha hb
    | true =>
      simp only [d17199, d201514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53594 q ha hb
  have h2 (q : Pattern) (ha : d17200 q = 1) (hb : d198467 q = 1) : d201515 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17200, d201515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17200, d201515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17201 q = 1) (hb : d198467 q = 1) : d201516 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17201, d201516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17201, d201516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17202 q = 1) (hb : d198467 q = 1) : d201517 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17202, d201517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17202, d201517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17203 q = 1) (hb : d198467 q = 1) : d201518 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17203, d201518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17203, d201518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171208 q = 1) (hb : d198467 q = 1) : d201901 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171208, d201901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171208, d201901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53675 (p : Pattern) (ha : d171215 p = 1) (hb : d198467 p = 1) : d201653 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17397 q = 1) (hb : d198467 q = 1) : d201638 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17397, d201638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53630 q ha hb
    | true =>
      simp only [d17397, d201638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53602 q ha hb
  have h2 (q : Pattern) (ha : d17398 q = 1) (hb : d198467 q = 1) : d201639 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17398, d201639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17398, d201639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17399 q = 1) (hb : d198467 q = 1) : d201640 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17399, d201640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17399, d201640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17400 q = 1) (hb : d198467 q = 1) : d201643 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17400, d201643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53602 q ha hb
    | true =>
      simp only [d17400, d201643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53628 q ha hb
  have h5 (q : Pattern) (ha : d17401 q = 1) (hb : d198467 q = 1) : d201644 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17401, d201644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17401, d201644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17402 q = 1) (hb : d198467 q = 1) : d201645 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17402, d201645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17402, d201645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17403 q = 1) (hb : d198467 q = 1) : d201646 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17403, d201646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17403, d201646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17417 q = 1) (hb : d198467 q = 1) : d201643 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17417, d201643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53602 q ha hb
    | true =>
      simp only [d17417, d201643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53601 q ha hb
  have h9 (q : Pattern) (ha : d17418 q = 1) (hb : d198467 q = 1) : d201644 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17418, d201644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17418, d201644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17419 q = 1) (hb : d198467 q = 1) : d201645 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17419, d201645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17419, d201645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17420 q = 1) (hb : d198467 q = 1) : d201651 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17420, d201651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17420, d201651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d171214 q = 1) (hb : d198467 q = 1) : d201652 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d171214, d201652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171214, d201652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d171215 q = 1) (hb : d198467 q = 1) : d201653 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d171215, d201653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171215, d201653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro53676 (p : Pattern) (ha : d171221 p = 1) (hb : d198467 p = 1) : d201667 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171216 q = 1) (hb : d198467 q = 1) : d201654 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d171216, d201654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53675 q ha hb
    | true =>
      simp only [d171216, d201654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d171217 q = 1) (hb : d198467 q = 1) : d201655 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d171217, d201655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171217, d201655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17423 q = 1) (hb : d198467 q = 1) : d201662 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17423, d201662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53603 q ha hb
    | true =>
      simp only [d17423, d201662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17424 q = 1) (hb : d198467 q = 1) : d201663 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17424, d201663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17424, d201663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171218 q = 1) (hb : d198467 q = 1) : d201664 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d171218, d201664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171218, d201664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171219 q = 1) (hb : d198467 q = 1) : d201665 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d171219, d201665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171219, d201665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d171220 q = 1) (hb : d198467 q = 1) : d201666 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d171220, d201666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171220, d201666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d171221 q = 1) (hb : d198467 q = 1) : d201667 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d171221, d201667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171221, d201667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro53677 (p : Pattern) (ha : d171227 p = 1) (hb : d198467 p = 1) : d201912 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171222 q = 1) (hb : d198467 q = 1) : d201907 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d171222, d201907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53676 q ha hb
    | true =>
      simp only [d171222, d201907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53604 q ha hb
  have h2 (q : Pattern) (ha : d171223 q = 1) (hb : d198467 q = 1) : d201908 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d171223, d201908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171223, d201908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d171224 q = 1) (hb : d198467 q = 1) : d201909 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d171224, d201909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171224, d201909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171225 q = 1) (hb : d198467 q = 1) : d201910 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d171225, d201910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171225, d201910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171226 q = 1) (hb : d198467 q = 1) : d201911 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d171226, d201911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171226, d201911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171227 q = 1) (hb : d198467 q = 1) : d201912 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171227, d201912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171227, d201912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53678 (p : Pattern) (ha : d171233 p = 1) (hb : d198467 p = 1) : d201918 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17205 q = 1) (hb : d198467 q = 1) : d201520 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17205, d201520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53592 q ha hb
    | true =>
      simp only [d17205, d201520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53595 q ha hb
  have h2 (q : Pattern) (ha : d17206 q = 1) (hb : d198467 q = 1) : d201521 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d17206, d201521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17206, d201521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d171206 q = 1) (hb : d198467 q = 1) : d201899 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171206, d201899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171206, d201899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171207 q = 1) (hb : d198467 q = 1) : d201900 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171207, d201900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171207, d201900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171209 q = 1) (hb : d198467 q = 1) : d201902 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171209, d201902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171209, d201902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53674 q ha hb
  have h6 (q : Pattern) (ha : d171210 q = 1) (hb : d198467 q = 1) : d201903 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171210, d201903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171210, d201903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d171211 q = 1) (hb : d198467 q = 1) : d201904 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171211, d201904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171211, d201904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d171212 q = 1) (hb : d198467 q = 1) : d201905 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171212, d201905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171212, d201905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d171213 q = 1) (hb : d198467 q = 1) : d201906 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171213, d201906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171213, d201906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d171228 q = 1) (hb : d198467 q = 1) : d201913 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171228, d201913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171228, d201913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53677 q ha hb
  have h11 (q : Pattern) (ha : d171229 q = 1) (hb : d198467 q = 1) : d201914 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171229, d201914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d171229, d201914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d171230 q = 1) (hb : d198467 q = 1) : d201915 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171230, d201915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d171230, d201915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d171231 q = 1) (hb : d198467 q = 1) : d201916 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171231, d201916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171231, d201916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d171232 q = 1) (hb : d198467 q = 1) : d201917 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171232, d201917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d171232, d201917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d171233 q = 1) (hb : d198467 q = 1) : d201918 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d171233, d201918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d171233, d201918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro53679 (p : Pattern) (ha : d171239 p = 1) (hb : d198467 p = 1) : d201924 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171234 q = 1) (hb : d198467 q = 1) : d201919 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d171234, d201919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171234, d201919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53678 q ha hb
  have h2 (q : Pattern) (ha : d171235 q = 1) (hb : d198467 q = 1) : d201920 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d171235, d201920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171235, d201920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d171236 q = 1) (hb : d198467 q = 1) : d201921 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d171236, d201921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171236, d201921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d171237 q = 1) (hb : d198467 q = 1) : d201922 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d171237, d201922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171237, d201922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171238 q = 1) (hb : d198467 q = 1) : d201923 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d171238, d201923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171238, d201923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171239 q = 1) (hb : d198467 q = 1) : d201924 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d171239, d201924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171239, d201924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53680 (p : Pattern) (ha : d171245 p = 1) (hb : d198467 p = 1) : d201930 p = 1 := by
  have h0 (q : Pattern) (ha : d171102 q = 1) (hb : d198467 q = 1) : d201811 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d171102, d201811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53653 q ha hb
    | true =>
      simp only [d171102, d201811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53657 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d171129 q = 1) (hb : d198467 q = 1) : d201838 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d171129, d201838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171129, d201838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53661 q ha hb
  have h3 (q : Pattern) (ha : d171130 q = 1) (hb : d198467 q = 1) : d201839 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d171130, d201839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171130, d201839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d171165 q = 1) (hb : d198467 q = 1) : d201866 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d171165, d201866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171165, d201866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53667 q ha hb
  have h5 (q : Pattern) (ha : d171166 q = 1) (hb : d198467 q = 1) : d201867 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d171166, d201867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171166, d201867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171167 q = 1) (hb : d198467 q = 1) : d201868 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d171167, d201868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171167, d201868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d171202 q = 1) (hb : d198467 q = 1) : d201895 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d171202, d201895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171202, d201895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53673 q ha hb
  have h8 (q : Pattern) (ha : d171203 q = 1) (hb : d198467 q = 1) : d201896 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d171203, d201896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171203, d201896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d171204 q = 1) (hb : d198467 q = 1) : d201897 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d171204, d201897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171204, d201897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d171205 q = 1) (hb : d198467 q = 1) : d201898 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d171205, d201898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171205, d201898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d171240 q = 1) (hb : d198467 q = 1) : d201925 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d171240, d201925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171240, d201925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53679 q ha hb
  have h12 (q : Pattern) (ha : d171241 q = 1) (hb : d198467 q = 1) : d201926 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d171241, d201926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171241, d201926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d171242 q = 1) (hb : d198467 q = 1) : d201927 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d171242, d201927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171242, d201927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d171243 q = 1) (hb : d198467 q = 1) : d201928 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d171243, d201928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171243, d201928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d171244 q = 1) (hb : d198467 q = 1) : d201929 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d171244, d201929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d171244, d201929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d171245 q = 1) (hb : d198467 q = 1) : d201930 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d171245, d201930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d171245, d201930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro53681 (p : Pattern) (ha : d171251 p = 1) (hb : d198467 p = 1) : d201936 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171246 q = 1) (hb : d198467 q = 1) : d201931 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d171246, d201931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53680 q ha hb
    | true =>
      simp only [d171246, d201931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d171247 q = 1) (hb : d198467 q = 1) : d201932 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d171247, d201932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171247, d201932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d171248 q = 1) (hb : d198467 q = 1) : d201933 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d171248, d201933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171248, d201933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171249 q = 1) (hb : d198467 q = 1) : d201934 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d171249, d201934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171249, d201934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d171250 q = 1) (hb : d198467 q = 1) : d201935 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d171250, d201935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171250, d201935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d171251 q = 1) (hb : d198467 q = 1) : d201936 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d171251, d201936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171251, d201936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53682 (p : Pattern) (ha : d171257 p = 1) (hb : d198467 p = 1) : d201942 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171252 q = 1) (hb : d198467 q = 1) : d201937 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d171252, d201937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53681 q ha hb
    | true =>
      simp only [d171252, d201937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d171253 q = 1) (hb : d198467 q = 1) : d201938 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d171253, d201938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171253, d201938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d171254 q = 1) (hb : d198467 q = 1) : d201939 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d171254, d201939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171254, d201939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171255 q = 1) (hb : d198467 q = 1) : d201940 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d171255, d201940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171255, d201940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d171256 q = 1) (hb : d198467 q = 1) : d201941 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d171256, d201941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171256, d201941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d171257 q = 1) (hb : d198467 q = 1) : d201942 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d171257, d201942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171257, d201942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53683 (p : Pattern) (ha : d171263 p = 1) (hb : d212559 p = 1) : d201948 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171258 q = 1) (hb : d198467 q = 1) : d201943 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d171258, d201943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53682 q ha hb
    | true =>
      simp only [d171258, d201943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d171259 q = 1) (hb : d198467 q = 1) : d201944 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d171259, d201944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171259, d201944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d171260 q = 1) (hb : d198467 q = 1) : d201945 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d171260, d201945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171260, d201945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171261 q = 1) (hb : d198467 q = 1) : d201946 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d171261, d201946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171261, d201946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d171262 q = 1) (hb : d198467 q = 1) : d201947 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d171262, d201947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171262, d201947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d171263 q = 1) (hb : d212559 q = 1) : d201948 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d171263, d212559, d201948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171263, d212559, d201948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro53684 (p : Pattern) (ha : d171269 p = 1) (hb : d212559 p = 1) : d201954 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d212559 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171264 q = 1) (hb : d212559 q = 1) : d201949 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d171264, d201949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53683 q ha hb
    | true =>
      simp only [d171264, d201949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d171265 q = 1) (hb : d212559 q = 1) : d201950 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d171265, d201950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171265, d201950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d171266 q = 1) (hb : d212559 q = 1) : d201951 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d171266, d201951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171266, d201951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171267 q = 1) (hb : d212559 q = 1) : d201952 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d171267, d201952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171267, d201952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d171268 q = 1) (hb : d212559 q = 1) : d201953 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d171268, d201953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171268, d201953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d171269 q = 1) (hb : d212559 q = 1) : d201954 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d171269, d201954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171269, d201954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53685 (p : Pattern) (ha : d171275 p = 1) (hb : d212559 p = 1) : d201960 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d212559 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171270 q = 1) (hb : d212559 q = 1) : d201955 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d171270, d201955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53684 q ha hb
    | true =>
      simp only [d171270, d201955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d171271 q = 1) (hb : d212559 q = 1) : d201956 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d171271, d201956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171271, d201956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d171272 q = 1) (hb : d212559 q = 1) : d201957 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d171272, d201957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171272, d201957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171273 q = 1) (hb : d212559 q = 1) : d201958 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d171273, d201958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171273, d201958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d171274 q = 1) (hb : d212559 q = 1) : d201959 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d171274, d201959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171274, d201959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d171275 q = 1) (hb : d212559 q = 1) : d201960 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d171275, d201960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171275, d201960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53686 (p : Pattern) (ha : d171281 p = 1) (hb : d212559 p = 1) : d201966 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d212559 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171276 q = 1) (hb : d212559 q = 1) : d201961 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d171276, d201961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53685 q ha hb
    | true =>
      simp only [d171276, d201961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d171277 q = 1) (hb : d212559 q = 1) : d201962 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d171277, d201962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171277, d201962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d171278 q = 1) (hb : d212559 q = 1) : d201963 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d171278, d201963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171278, d201963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171279 q = 1) (hb : d212559 q = 1) : d201964 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d171279, d201964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171279, d201964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d171280 q = 1) (hb : d212559 q = 1) : d201965 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d171280, d201965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171280, d201965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d171281 q = 1) (hb : d212559 q = 1) : d201966 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d171281, d201966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171281, d201966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53687 (p : Pattern) (ha : d171287 p = 1) (hb : d212559 p = 1) : d201972 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d212559 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171282 q = 1) (hb : d212559 q = 1) : d201967 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d171282, d201967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53686 q ha hb
    | true =>
      simp only [d171282, d201967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d171283 q = 1) (hb : d212559 q = 1) : d201968 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d171283, d201968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171283, d201968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d171284 q = 1) (hb : d212559 q = 1) : d201969 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d171284, d201969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171284, d201969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171285 q = 1) (hb : d212559 q = 1) : d201970 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d171285, d201970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171285, d201970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d171286 q = 1) (hb : d212559 q = 1) : d201971 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d171286, d201971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171286, d201971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d171287 q = 1) (hb : d212559 q = 1) : d201972 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d171287, d201972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171287, d201972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53688 (p : Pattern) (ha : d36 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128486 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d33 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, d128487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, d128487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d34 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d35 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d35, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d35, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d36 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d36, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro53689 (p : Pattern) (ha : d42 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53688 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d41 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53690 (p : Pattern) (ha : d48 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53689 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d47 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d48 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d48, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d48, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53691 (p : Pattern) (ha : d49 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53688 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d41 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d49 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d49, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d49, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53692 (p : Pattern) (ha : d55 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53689 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d47 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d50 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53691 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d51 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d52 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d55 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d55, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d55, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro53693 (p : Pattern) (ha : d60 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d50 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53691 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d52 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d60 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d60, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53694 (p : Pattern) (ha : d77 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128486 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d73 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d74 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d128487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, d128487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d75 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d76, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d77 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d77, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro53695 (p : Pattern) (ha : d83 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53694 q ha hb
    | true =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d79 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d80 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d81 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d81, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d82, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d83 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53696 (p : Pattern) (ha : d89 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53695 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d86 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d86, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d87 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d87, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d88 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53697 (p : Pattern) (ha : d95 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53690 q ha hb
    | true =>
      simp only [d56, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53692 q ha hb
  have h2 (q : Pattern) (ha : d57 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d57, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d59 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d59, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53693 q ha hb
  have h6 (q : Pattern) (ha : d62 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d63 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d63, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d64 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d64, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d64, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d65 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d65, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d65, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d90 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d90, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53696 q ha hb
  have h11 (q : Pattern) (ha : d91 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d91, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d91, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d92 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d93 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d93, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d94 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d95 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d95, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d95, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro53698 (p : Pattern) (ha : d104 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53689 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d100 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d104 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53699 (p : Pattern) (ha : d111 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53689 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d100 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d50 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53691 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d107 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d109 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d110 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d111 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro53700 (p : Pattern) (ha : d213 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53689 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d100 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d213 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53701 (p : Pattern) (ha : d150 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128486 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d146 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d147 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d128487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d128487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d32 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d33 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, d128487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, d128487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d148 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d34 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d149 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro53702 (p : Pattern) (ha : d203 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53701 q ha hb
    | true =>
      simp only [d151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53688 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d153 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d154 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d155 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d203 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro53703 (p : Pattern) (ha : d4349 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d204 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53702 q ha hb
    | true =>
      simp only [d204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53691 q ha hb
  have h2 (q : Pattern) (ha : d4340 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d50 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53691 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4341 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4342 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4343 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4349 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53704 (p : Pattern) (ha : d237 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128486 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d233 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d234 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d128487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d128487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d73 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d74 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d128487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, d128487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d235 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d75 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d236 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d237 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro53705 (p : Pattern) (ha : d243 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53704 q ha hb
    | true =>
      simp only [d238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53694 q ha hb
    | true =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d79 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d240 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d241 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d242 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d243 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro53706 (p : Pattern) (ha : d4359 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d244 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53705 q ha hb
    | true =>
      simp only [d244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53695 q ha hb
  have h2 (q : Pattern) (ha : d4355 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d84 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53695 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4356 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4357 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4358 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4359 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53707 (p : Pattern) (ha : d116 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53688 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53708 (p : Pattern) (ha : d123 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53688 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d121 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53709 (p : Pattern) (ha : d156 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53701 q ha hb
    | true =>
      simp only [d151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53688 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d153 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d154 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d155 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d156 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53710 (p : Pattern) (ha : d51643 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53707 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53708 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d157 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53709 q ha hb
    | true =>
      simp only [d157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53689 q ha hb
  have h9 (q : Pattern) (ha : d4335 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53689 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4336 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d51641 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51642 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d51643 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro53711 (p : Pattern) (ha : d194 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53688 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53712 (p : Pattern) (ha : d199 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53688 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d121 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d199 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53713 (p : Pattern) (ha : d51646 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53707 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53708 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d157 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53709 q ha hb
    | true =>
      simp only [d157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53689 q ha hb
  have h9 (q : Pattern) (ha : d4335 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53689 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4336 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d51641 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51642 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d195 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53711 q ha hb
    | true =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d196 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d197 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d198 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d200 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53712 q ha hb
    | true =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d201 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d202 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d204 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53702 q ha hb
    | true =>
      simp only [d204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53691 q ha hb
  have h23 (q : Pattern) (ha : d4340 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d4340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d50 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53691 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d51 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d4341 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d4341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d51644 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d51644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d51645 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d51645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d51646 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d51646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro53714 (p : Pattern) (ha : d51652 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53698 q ha hb
  have h2 (q : Pattern) (ha : d106 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53698 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53699 q ha hb
  have h4 (q : Pattern) (ha : d113 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d114 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51647 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53710 q ha hb
    | true =>
      simp only [d51647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53713 q ha hb
  have h7 (q : Pattern) (ha : d214 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53700 q ha hb
    | true =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d51648 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51649 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d51650 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4350 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53703 q ha hb
  have h12 (q : Pattern) (ha : d4351 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d4352 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d4353 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d51651 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d51651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d4360 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53706 q ha hb
  have h17 (q : Pattern) (ha : d4361 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d4361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d4362 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d4362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d4363 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d4363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d4364 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d4364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d51652 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d51652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro53715 (p : Pattern) (ha : d284 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d157 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53709 q ha hb
    | true =>
      simp only [d157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53689 q ha hb
  have h2 (q : Pattern) (ha : d280 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d281 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d282 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d283 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d284 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53716 (p : Pattern) (ha : d291 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d157 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53709 q ha hb
    | true =>
      simp only [d157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53689 q ha hb
  have h2 (q : Pattern) (ha : d280 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d281 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d282 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d283 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d204 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53702 q ha hb
    | true =>
      simp only [d204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53691 q ha hb
  have h7 (q : Pattern) (ha : d287 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d288 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d289 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d290 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d291 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro53717 (p : Pattern) (ha : d397 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d157 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53709 q ha hb
    | true =>
      simp only [d157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53689 q ha hb
  have h2 (q : Pattern) (ha : d280 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d281 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d282 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d283 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53689 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d100 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d102 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d103 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d397 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro53718 (p : Pattern) (ha : d406 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d50 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53691 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d107 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d110 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d406 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53719 (p : Pattern) (ha : d462 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53695 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d458 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d459 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d460 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d461 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d462 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53720 (p : Pattern) (ha : d296 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53701 q ha hb
    | true =>
      simp only [d151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53688 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d153 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d154 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d295 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d296 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53721 (p : Pattern) (ha : d303 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53701 q ha hb
    | true =>
      simp only [d151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53688 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d153 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d301 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d302 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d303 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53722 (p : Pattern) (ha : d4736 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53701 q ha hb
    | true =>
      simp only [d151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4733 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4734 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4735 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4736 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d4736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53723 (p : Pattern) (ha : d15972 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128486 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15968 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15969 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15969, d128487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15969, d128487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d146 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d147 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d128487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d128487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d15970 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d32 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d33 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, d128487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, d128487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d148 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15971 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d15972 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro53724 (p : Pattern) (ha : d15978 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15973 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53723 q ha hb
    | true =>
      simp only [d15973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15974 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d151 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53701 q ha hb
    | true =>
      simp only [d151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d152 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15975 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15976 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15977 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15978 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53725 (p : Pattern) (ha : d128195 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d297 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53720 q ha hb
    | true =>
      simp only [d297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53707 q ha hb
  have h2 (q : Pattern) (ha : d298 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d299 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d300 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d304 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53721 q ha hb
    | true =>
      simp only [d304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53708 q ha hb
  have h6 (q : Pattern) (ha : d305 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15979 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53724 q ha hb
    | true =>
      simp only [d15979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53709 q ha hb
  have h9 (q : Pattern) (ha : d128191 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d4737 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53722 q ha hb
    | true =>
      simp only [d4737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5350 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128192 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128193 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128194 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128195 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro53726 (p : Pattern) (ha : d376 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53701 q ha hb
    | true =>
      simp only [d151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53688 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d153 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d154 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d295 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d376 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro53727 (p : Pattern) (ha : d381 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53701 q ha hb
    | true =>
      simp only [d151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53688 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d153 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d301 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d302 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d381 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro53728 (p : Pattern) (ha : d5355 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53701 q ha hb
    | true =>
      simp only [d151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4733 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4734 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4735 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5355 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53729 (p : Pattern) (ha : d15985 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15973 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53723 q ha hb
    | true =>
      simp only [d15973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15974 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d151 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53701 q ha hb
    | true =>
      simp only [d151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d152 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15975 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15976 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15977 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15985 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro53730 (p : Pattern) (ha : d128200 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d297 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53720 q ha hb
    | true =>
      simp only [d297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53707 q ha hb
  have h2 (q : Pattern) (ha : d298 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d299 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d300 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d304 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53721 q ha hb
    | true =>
      simp only [d304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53708 q ha hb
  have h6 (q : Pattern) (ha : d305 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15979 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53724 q ha hb
    | true =>
      simp only [d15979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53709 q ha hb
  have h9 (q : Pattern) (ha : d128191 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d4737 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53722 q ha hb
    | true =>
      simp only [d4737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5350 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128192 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128193 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128194 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d377 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53726 q ha hb
    | true =>
      simp only [d377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53711 q ha hb
  have h16 (q : Pattern) (ha : d378 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d379 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d380 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d382 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53727 q ha hb
    | true =>
      simp only [d382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53712 q ha hb
  have h20 (q : Pattern) (ha : d383 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d384 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d15986 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53729 q ha hb
    | true =>
      simp only [d15986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53702 q ha hb
  have h23 (q : Pattern) (ha : d128196 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d128196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d5356 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53728 q ha hb
    | true =>
      simp only [d5356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d5357 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d5357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d128197 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d128197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d128198 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d128199 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d128199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d128200 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro53731 (p : Pattern) (ha : d128207 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15986 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53729 q ha hb
    | true =>
      simp only [d15986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53702 q ha hb
  have h2 (q : Pattern) (ha : d128196 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5356 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53728 q ha hb
    | true =>
      simp only [d5356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5357 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128197 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128205 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128206 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128207 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53732 (p : Pattern) (ha : d5377 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53704 q ha hb
    | true =>
      simp only [d238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5374 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5375 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5376 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5377 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53733 (p : Pattern) (ha : d16010 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128486 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16006 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16007 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, d128487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16007, d128487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d233 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d234 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d128487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d128487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d16008 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d73 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d74 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d128487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, d128487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d235 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d16009 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d16010 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro53734 (p : Pattern) (ha : d16016 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16011 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53733 q ha hb
    | true =>
      simp only [d16011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16012 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d238 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53704 q ha hb
    | true =>
      simp only [d238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d239 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16013 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16014 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16015 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16016 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro53735 (p : Pattern) (ha : d128217 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16017 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53734 q ha hb
    | true =>
      simp only [d16017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53705 q ha hb
  have h2 (q : Pattern) (ha : d128213 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5378 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53732 q ha hb
    | true =>
      simp only [d5378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5379 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128214 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128215 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128216 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128217 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53736 (p : Pattern) (ha : d128223 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53715 q ha hb
  have h2 (q : Pattern) (ha : d286 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d292 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53715 q ha hb
    | true =>
      simp only [d292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53716 q ha hb
  have h4 (q : Pattern) (ha : d293 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d294 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128201 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53725 q ha hb
    | true =>
      simp only [d128201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53730 q ha hb
  have h7 (q : Pattern) (ha : d398 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53717 q ha hb
    | true =>
      simp only [d398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53699 q ha hb
  have h8 (q : Pattern) (ha : d128202 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128203 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d128204 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128208 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53731 q ha hb
  have h12 (q : Pattern) (ha : d407 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53718 q ha hb
  have h13 (q : Pattern) (ha : d128209 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128210 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d128211 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d128212 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d128218 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53735 q ha hb
  have h18 (q : Pattern) (ha : d463 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53719 q ha hb
  have h19 (q : Pattern) (ha : d128219 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d128220 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d128220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d128221 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d128221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d128222 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d128223 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro53737 (p : Pattern) (ha : d128229 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53697 q ha hb
  have h2 (q : Pattern) (ha : d97 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d98 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51653 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53714 q ha hb
  have h6 (q : Pattern) (ha : d51654 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51655 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51656 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51657 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128224 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53736 q ha hb
  have h11 (q : Pattern) (ha : d128225 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d128226 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128227 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128228 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128229 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro53738 (p : Pattern) (ha : d481 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128486 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d146 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d147 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d128487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d128487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d475 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d480 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d481 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro53739 (p : Pattern) (ha : d491 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53738 q ha hb
    | true =>
      simp only [d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d490 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d491 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53740 (p : Pattern) (ha : d501 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53738 q ha hb
    | true =>
      simp only [d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d490 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d501 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53741 (p : Pattern) (ha : d644 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d633 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53739 q ha hb
    | true =>
      simp only [d633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d634 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d635 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d636 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d637 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d639 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53740 q ha hb
    | true =>
      simp only [d639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d640 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d641 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d642 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d643 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d644 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro53742 (p : Pattern) (ha : d653 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d639 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53740 q ha hb
    | true =>
      simp only [d639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d640 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d641 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d642 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d643 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d653 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53743 (p : Pattern) (ha : d683 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128486 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d233 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d234 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d128487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d128487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d673 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d682 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d683 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro53744 (p : Pattern) (ha : d730 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d684 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53743 q ha hb
    | true =>
      simp only [d684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d685 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d727 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d728 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d729 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d730 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro53745 (p : Pattern) (ha : d736 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d731 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53744 q ha hb
    | true =>
      simp only [d731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d732 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d733 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d734 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d735 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d736 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53746 (p : Pattern) (ha : d16036 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128486 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15968 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15969 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15969, d128487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15969, d128487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d146 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d147 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d128487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d128487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d15970 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d475 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16035 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d16036 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro53747 (p : Pattern) (ha : d16042 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53746 q ha hb
    | true =>
      simp only [d16037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53738 q ha hb
    | true =>
      simp only [d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16040 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16041 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16042 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro53748 (p : Pattern) (ha : d16048 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16043 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53747 q ha hb
    | true =>
      simp only [d16043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53739 q ha hb
  have h2 (q : Pattern) (ha : d16044 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16045 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16046 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16047 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16048 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro53749 (p : Pattern) (ha : d16051 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53746 q ha hb
    | true =>
      simp only [d16037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53738 q ha hb
    | true =>
      simp only [d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16040 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16041 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16051 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
end NetHack.Soko22Hazard87
