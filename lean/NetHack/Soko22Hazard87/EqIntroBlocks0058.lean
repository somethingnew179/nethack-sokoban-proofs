import NetHack.Soko22Hazard87.EqIntroBlocks0057
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro14500 (p : Pattern) (selected : d15248 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15160 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14481 q selected
    | true =>
      simp only [d15160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14482 q selected
  have h2 (q : Pattern) (selected : d15161 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15162 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d15167 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14482 q selected
    | true =>
      simp only [d15167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14483 q selected
  have h5 (q : Pattern) (selected : d15168 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15169 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d15170 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d15246 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d15247 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d15248 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d15248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro14501 (p : Pattern) (selected : d15254 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15244 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14499 q selected
    | true =>
      simp only [d15244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15245 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15249 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14500 q selected
    | true =>
      simp only [d15249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15250 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d15251 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15252 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15253 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15254 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14502 (p : Pattern) (selected : d15258 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15249 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14500 q selected
    | true =>
      simp only [d15249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15250 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15182 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14486 q selected
    | true =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15183 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d15255 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15256 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15257 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15258 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14503 (p : Pattern) (selected : d15264 p = 2) : d15154 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1726 q = 2) : d1555 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1726, d1555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro957 q selected
    | true =>
      simp only [d1726, d1555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1727 q = 2) : d1556 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1727, d1556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1727, d1556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1728 q = 2) : d1557 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1728, d1557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1728, d1557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1729 q = 2) : d1558 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1729, d1558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1729, d1558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15260 q = 2) : d15150 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15260, d15150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d15260, d15150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10200 q = 2) : d10063 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10200, d10063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10619 q selected
    | true =>
      simp only [d10200, d10063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10202 q = 2) : d10065 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10202, d10065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10202, d10065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15261 q = 2) : d15151 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15261, d15151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15261, d15151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d15262 q = 2) : d15152 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15262, d15152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d15262, d15152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15263 q = 2) : d15153 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15263, d15153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d15263, d15153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d15264 q = 2) : d15154 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15264, d15154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15264, d15154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14504 (p : Pattern) (selected : d15269 p = 2) : d15159 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1741 q = 2) : d1570 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1741, d1570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro960 q selected
    | true =>
      simp only [d1741, d1570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1742 q = 2) : d1571 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1742, d1571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1742, d1571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1743 q = 2) : d1572 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1743, d1572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1743, d1572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1744 q = 2) : d1573 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1744, d1573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1744, d1573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15265 q = 2) : d15155 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15265, d15155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d15265, d15155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10215 q = 2) : d10085 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10215, d10085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10620 q selected
    | true =>
      simp only [d10215, d10085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10217 q = 2) : d10087 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10217, d10087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10217, d10087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15266 q = 2) : d15156 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15266, d15156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15266, d15156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d15267 q = 2) : d15157 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15267, d15157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d15267, d15157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15268 q = 2) : d15158 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15268, d15158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d15268, d15158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d15269 q = 2) : d15159 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15269, d15159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15269, d15159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14505 (p : Pattern) (selected : d15276 p = 2) : d15166 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d10243 q = 2) : d5134 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10243, d5134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10624 q selected
    | true =>
      simp only [d10243, d5134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10245 q = 2) : d5135 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10245, d5135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10245, d5135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13383 q = 2) : d5136 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13383, d5136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13383, d5136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13384 q = 2) : d5137 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13384, d5137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13384, d5137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13385 q = 2) : d5138 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13385, d5138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13385, d5138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10255 q = 2) : d10135 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10255, d10135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10625 q selected
    | true =>
      simp only [d10255, d10135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10257 q = 2) : d10137 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10257, d10137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10257, d10137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15273 q = 2) : d15163 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15273, d15163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15273, d15163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d15274 q = 2) : d15164 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15274, d15164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d15274, d15164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15275 q = 2) : d15165 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15275, d15165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d15275, d15165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d15276 q = 2) : d15166 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15276, d15166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15276, d15166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14506 (p : Pattern) (selected : d15281 p = 2) : d15171 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1753 q = 2) : d1582 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1753, d1582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro961 q selected
    | true =>
      simp only [d1753, d1582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1754 q = 2) : d1583 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1754, d1583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1754, d1583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1755 q = 2) : d1584 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1755, d1584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1755, d1584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1756 q = 2) : d1585 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1756, d1585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1756, d1585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1759 q = 2) : d1588 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1759, d1588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1759, d1588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10255 q = 2) : d10135 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10255, d10135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10625 q selected
    | true =>
      simp only [d10255, d10135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10257 q = 2) : d10137 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10257, d10137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10257, d10137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15273 q = 2) : d15163 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15273, d15163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15273, d15163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d15274 q = 2) : d15164 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15274, d15164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d15274, d15164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15275 q = 2) : d15165 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15275, d15165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d15275, d15165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d15281 q = 2) : d15171 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15281, d15171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15281, d15171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14507 (p : Pattern) (selected : d15287 p = 2) : d15177 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15270 q = 2) : d15160 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15270, d15160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14503 q selected
    | true =>
      simp only [d15270, d15160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14504 q selected
  have h2 (q : Pattern) (selected : d15271 q = 2) : d15161 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15271, d15161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15271, d15161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15272 q = 2) : d15162 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15272, d15162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15272, d15162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d15277 q = 2) : d15167 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15277, d15167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14504 q selected
    | true =>
      simp only [d15277, d15167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14505 q selected
  have h5 (q : Pattern) (selected : d15278 q = 2) : d15168 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15278, d15168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15278, d15168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15279 q = 2) : d15169 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15279, d15169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15279, d15169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d15280 q = 2) : d15170 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15280, d15170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15280, d15170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d15282 q = 2) : d15172 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15282, d15172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14504 q selected
    | true =>
      simp only [d15282, d15172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14506 q selected
  have h9 (q : Pattern) (selected : d15283 q = 2) : d15173 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15283, d15173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15283, d15173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d15284 q = 2) : d15174 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15284, d15174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15284, d15174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d15285 q = 2) : d15175 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15285, d15175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d15285, d15175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d15286 q = 2) : d15176 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15286, d15176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15286, d15176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d15287 q = 2) : d15177 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15287, d15177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15287, d15177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro14508 (p : Pattern) (selected : d15291 p = 2) : d15181 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15282 q = 2) : d15172 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15282, d15172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14504 q selected
    | true =>
      simp only [d15282, d15172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14506 q selected
  have h2 (q : Pattern) (selected : d15283 q = 2) : d15173 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15283, d15173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15283, d15173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15284 q = 2) : d15174 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15284, d15174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15284, d15174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d15285 q = 2) : d15175 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15285, d15175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15285, d15175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15290 q = 2) : d15180 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15290, d15180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d15290, d15180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d15291 q = 2) : d15181 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15291, d15181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15291, d15181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14509 (p : Pattern) (selected : d15297 p = 2) : d15187 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15288 q = 2) : d15178 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15288, d15178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14507 q selected
    | true =>
      simp only [d15288, d15178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15289 q = 2) : d15179 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15289, d15179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15289, d15179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15292 q = 2) : d15182 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15292, d15182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14508 q selected
    | true =>
      simp only [d15292, d15182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15293 q = 2) : d15183 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15293, d15183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15293, d15183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d15294 q = 2) : d15184 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15294, d15184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15294, d15184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15295 q = 2) : d15185 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15295, d15185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15295, d15185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15296 q = 2) : d15186 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15296, d15186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15296, d15186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15297 q = 2) : d15187 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15297, d15187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15297, d15187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14510 (p : Pattern) (selected : d15301 p = 2) : d15191 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15292 q = 2) : d15182 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15292, d15182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14508 q selected
    | true =>
      simp only [d15292, d15182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15293 q = 2) : d15183 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15293, d15183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15293, d15183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15298 q = 2) : d15188 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15298, d15188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15298, d15188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15299 q = 2) : d15189 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15299, d15189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15299, d15189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15300 q = 2) : d15190 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15300, d15190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d15300, d15190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d15301 q = 2) : d15191 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15301, d15191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15301, d15191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14511 (p : Pattern) (selected : d15309 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15160 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14481 q selected
    | true =>
      simp only [d15160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14482 q selected
  have h2 (q : Pattern) (selected : d15161 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15162 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d15167 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14482 q selected
    | true =>
      simp only [d15167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14483 q selected
  have h5 (q : Pattern) (selected : d15168 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15169 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d15170 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d15304 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14482 q selected
    | true =>
      simp only [d15304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13579 q selected
  have h9 (q : Pattern) (selected : d15305 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d15306 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d15307 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d15307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d15308 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d15309 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro14512 (p : Pattern) (selected : d15315 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15310 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14511 q selected
    | true =>
      simp only [d15310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15311 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15312 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15313 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15314 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d15314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d15315 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14513 (p : Pattern) (selected : d15321 p = 2) : d15197 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15215 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14493 q selected
    | true =>
      simp only [d15215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14494 q selected
  have h2 (q : Pattern) (selected : d15216 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15217 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15218 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d15225 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14495 q selected
    | true =>
      simp only [d15225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14496 q selected
  have h6 (q : Pattern) (selected : d15226 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d15227 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15259 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14501 q selected
    | true =>
      simp only [d15259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14502 q selected
  have h9 (q : Pattern) (selected : d15302 q = 2) : d15192 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15302, d15192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14509 q selected
    | true =>
      simp only [d15302, d15192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14510 q selected
  have h10 (q : Pattern) (selected : d15303 q = 2) : d15193 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15303, d15193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d15303, d15193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d15316 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14512 q selected
    | true =>
      simp only [d15316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d15317 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d15317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d15318 q = 2) : d15194 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15318, d15194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d15318, d15194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d15319 q = 2) : d15195 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15319, d15195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15319, d15195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d15320 q = 2) : d15196 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15320, d15196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d15320, d15196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d15321 q = 2) : d15197 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15321, d15197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15321, d15197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro14514 (p : Pattern) (selected : d15322 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15178 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14485 q selected
    | true =>
      simp only [d15178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15179 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15182 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14486 q selected
    | true =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15183 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d15184 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15185 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15211 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d15322 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14515 (p : Pattern) (selected : d15323 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15182 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14486 q selected
    | true =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15183 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15188 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15189 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15213 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15323 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14516 (p : Pattern) (selected : d15328 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15178 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14485 q selected
    | true =>
      simp only [d15178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15179 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15182 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14486 q selected
    | true =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15183 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d15184 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15219 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d15220 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15328 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14517 (p : Pattern) (selected : d15329 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15182 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14486 q selected
    | true =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15183 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15188 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15222 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d15223 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d15223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d15329 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14518 (p : Pattern) (selected : d15333 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15244 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14499 q selected
    | true =>
      simp only [d15244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15245 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15249 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14500 q selected
    | true =>
      simp only [d15249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15250 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d15251 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15252 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15253 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15333 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14519 (p : Pattern) (selected : d15334 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15249 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14500 q selected
    | true =>
      simp only [d15249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15250 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15182 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14486 q selected
    | true =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15183 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d15255 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15256 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15257 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15334 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14520 (p : Pattern) (selected : d15336 p = 2) : d15200 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15288 q = 2) : d15178 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15288, d15178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14507 q selected
    | true =>
      simp only [d15288, d15178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15289 q = 2) : d15179 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15289, d15179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15289, d15179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15292 q = 2) : d15182 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15292, d15182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14508 q selected
    | true =>
      simp only [d15292, d15182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15293 q = 2) : d15183 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15293, d15183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15293, d15183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d15294 q = 2) : d15184 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15294, d15184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15294, d15184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15295 q = 2) : d15185 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15295, d15185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15295, d15185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15296 q = 2) : d15186 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15296, d15186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15296, d15186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15336 q = 2) : d15200 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15336, d15200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15336, d15200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14521 (p : Pattern) (selected : d15337 p = 2) : d15201 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15292 q = 2) : d15182 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15292, d15182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14508 q selected
    | true =>
      simp only [d15292, d15182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15293 q = 2) : d15183 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15293, d15183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15293, d15183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15298 q = 2) : d15188 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15298, d15188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15298, d15188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15299 q = 2) : d15189 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15299, d15189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15299, d15189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15300 q = 2) : d15190 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15300, d15190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d15300, d15190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d15337 q = 2) : d15201 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15337, d15201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15337, d15201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14522 (p : Pattern) (selected : d15340 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15310 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14511 q selected
    | true =>
      simp only [d15310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15311 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15312 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15313 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15314 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d15314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d15340 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14523 (p : Pattern) (selected : d15346 p = 2) : d15207 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15215 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14493 q selected
    | true =>
      simp only [d15215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14494 q selected
  have h2 (q : Pattern) (selected : d15216 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15217 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15218 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d15225 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14495 q selected
    | true =>
      simp only [d15225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14496 q selected
  have h6 (q : Pattern) (selected : d15226 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d15227 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15259 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14501 q selected
    | true =>
      simp only [d15259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14502 q selected
  have h9 (q : Pattern) (selected : d15302 q = 2) : d15192 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15302, d15192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14509 q selected
    | true =>
      simp only [d15302, d15192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14510 q selected
  have h10 (q : Pattern) (selected : d15303 q = 2) : d15193 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15303, d15193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d15303, d15193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d15316 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14512 q selected
    | true =>
      simp only [d15316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d15317 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d15317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d15318 q = 2) : d15194 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15318, d15194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d15318, d15194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d15319 q = 2) : d15195 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15319, d15195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15319, d15195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d15320 q = 2) : d15196 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15320, d15196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d15320, d15196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d15324 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14514 q selected
    | true =>
      simp only [d15324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14515 q selected
  have h17 (q : Pattern) (selected : d15325 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d15326 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d15326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d15327 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d15330 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14516 q selected
    | true =>
      simp only [d15330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14517 q selected
  have h21 (q : Pattern) (selected : d15331 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d15332 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d15332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d15335 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14518 q selected
    | true =>
      simp only [d15335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14519 q selected
  have h24 (q : Pattern) (selected : d15338 q = 2) : d15202 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15338, d15202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14520 q selected
    | true =>
      simp only [d15338, d15202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14521 q selected
  have h25 (q : Pattern) (selected : d15339 q = 2) : d15203 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15339, d15203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d15339, d15203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d15341 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14522 q selected
    | true =>
      simp only [d15341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d15342 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d15342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d15343 q = 2) : d15204 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15343, d15204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d15343, d15204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d15344 q = 2) : d15205 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15344, d15205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d15344, d15205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d15345 q = 2) : d15206 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15345, d15206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d15345, d15206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d15346 q = 2) : d15207 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15346, d15207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d15346, d15207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro14524 (p : Pattern) (selected : d15358 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15348 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14502 q selected
    | true =>
      simp only [d15348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14488 q selected
  have h2 (q : Pattern) (selected : d15349 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15350 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15351 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d15352 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15353 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14488 q selected
    | true =>
      simp only [d15353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15354 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d15355 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d15356 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d15357 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d15358 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14525 (p : Pattern) (selected : d15364 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15353 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14488 q selected
    | true =>
      simp only [d15353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15354 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15355 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15356 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d15357 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15359 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14491 q selected
    | true =>
      simp only [d15359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15360 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d15361 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d15362 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d15363 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d15364 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14526 (p : Pattern) (selected : d15371 p = 2) : d163564 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15335 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14518 q selected
    | true =>
      simp only [d15335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14519 q selected
  have h2 (q : Pattern) (selected : d15338 q = 2) : d15202 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15338, d15202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14520 q selected
    | true =>
      simp only [d15338, d15202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14521 q selected
  have h3 (q : Pattern) (selected : d15339 q = 2) : d15203 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15339, d15203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d15339, d15203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d15341 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14522 q selected
    | true =>
      simp only [d15341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15342 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d15342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d15343 q = 2) : d15204 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15343, d15204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15343, d15204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d15369 q = 2) : d15205 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15369, d15205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15369, d15205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d15370 q = 2) : d15206 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15370, d15206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15370, d15206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d15371 q = 2) : d163564 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15371, d163564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15371, d163564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro14527 (p : Pattern) (selected : d15373 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15359 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14491 q selected
    | true =>
      simp only [d15359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15360 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15361 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15362 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d15363 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15373 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14528 (p : Pattern) (selected : d15385 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1853 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro945 q selected
  have h2 (q : Pattern) (selected : d1665 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro945 q selected
    | true =>
      simp only [d1665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1854 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1666 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1855 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1856 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15379 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15380 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10597 q selected
  have h9 (q : Pattern) (selected : d10046 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10597 q selected
    | true =>
      simp only [d10046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15381 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d15381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d10048 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d10048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d15382 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d15382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d15383 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d15384 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d15384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d15385 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro14529 (p : Pattern) (selected : d15392 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1857 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro924 q selected
  have h2 (q : Pattern) (selected : d1555 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro924 q selected
    | true =>
      simp only [d1555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1858 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1556 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1859 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1860 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15386 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15387 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10599 q selected
  have h9 (q : Pattern) (selected : d10063 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10599 q selected
    | true =>
      simp only [d10063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15388 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d15388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d10065 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d10065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d15389 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d15389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d15390 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d15391 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d15391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d15392 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro14530 (p : Pattern) (selected : d15402 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13486 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10604 q selected
  have h2 (q : Pattern) (selected : d10099 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10604 q selected
    | true =>
      simp only [d10099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13487 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10101 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13488 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13489 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15396 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15397 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10602 q selected
  have h9 (q : Pattern) (selected : d10085 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10602 q selected
    | true =>
      simp only [d10085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15398 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d15398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d10087 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d10087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d15399 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d15399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d15400 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d15401 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d15401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d15402 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro14531 (p : Pattern) (selected : d15408 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1862 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro927 q selected
  have h2 (q : Pattern) (selected : d1570 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro927 q selected
    | true =>
      simp only [d1570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1863 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1571 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1864 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1865 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15407 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15397 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10602 q selected
  have h9 (q : Pattern) (selected : d10085 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10602 q selected
    | true =>
      simp only [d10085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15398 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d15398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d10087 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d10087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d15399 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d15399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d15400 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d15401 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d15401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d15408 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro14532 (p : Pattern) (selected : d15417 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d6496 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d6496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3858 q selected
  have h2 (q : Pattern) (selected : d5134 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3858 q selected
    | true =>
      simp only [d5134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d6497 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d6497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d6497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d5135 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d5135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6498 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d6498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d6499 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d6499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d6500 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d6500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d6500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15412 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10608 q selected
  have h9 (q : Pattern) (selected : d10135 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10608 q selected
    | true =>
      simp only [d10135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15413 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d15413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d10137 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d10137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d15414 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d15414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d15415 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d15416 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d15416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d15417 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro14533 (p : Pattern) (selected : d15423 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15393 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14528 q selected
    | true =>
      simp only [d15393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14529 q selected
  have h2 (q : Pattern) (selected : d15394 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15395 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d15403 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14529 q selected
    | true =>
      simp only [d15403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14530 q selected
  have h5 (q : Pattern) (selected : d15404 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15405 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d15406 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d15409 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14529 q selected
    | true =>
      simp only [d15409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14531 q selected
  have h9 (q : Pattern) (selected : d15410 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d15411 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d15418 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14531 q selected
    | true =>
      simp only [d15418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14532 q selected
  have h12 (q : Pattern) (selected : d15419 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d15420 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d15421 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d15421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d15422 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d15423 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d15423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro14534 (p : Pattern) (selected : d15428 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15409 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14529 q selected
    | true =>
      simp only [d15409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14531 q selected
  have h2 (q : Pattern) (selected : d15410 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15411 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d15418 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14531 q selected
    | true =>
      simp only [d15418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14532 q selected
  have h5 (q : Pattern) (selected : d15419 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15420 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d15421 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d15426 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d15427 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d15428 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d15428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro14535 (p : Pattern) (selected : d15434 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15424 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14533 q selected
    | true =>
      simp only [d15424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15425 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15429 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14534 q selected
    | true =>
      simp only [d15429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15430 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d15431 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15432 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15433 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15434 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14536 (p : Pattern) (selected : d15435 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1868 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro928 q selected
  have h2 (q : Pattern) (selected : d1582 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro928 q selected
    | true =>
      simp only [d1582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1869 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1583 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1870 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1871 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1877 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15412 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10608 q selected
  have h9 (q : Pattern) (selected : d10135 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10608 q selected
    | true =>
      simp only [d10135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15413 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d15413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d10137 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d10137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d15414 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d15414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d15415 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d15416 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d15416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d15435 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro14537 (p : Pattern) (selected : d15441 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15436 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14531 q selected
    | true =>
      simp only [d15436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14536 q selected
  have h2 (q : Pattern) (selected : d15437 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15438 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d15439 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15440 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d15440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d15441 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14538 (p : Pattern) (selected : d15447 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15429 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14534 q selected
    | true =>
      simp only [d15429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15430 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15442 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14537 q selected
    | true =>
      simp only [d15442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15443 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d15444 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15445 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15446 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15447 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14539 (p : Pattern) (selected : d15455 p = 2) : d15392 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1915 q = 2) : d1857 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1915, d1857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1915, d1857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro957 q selected
  have h2 (q : Pattern) (selected : d1726 q = 2) : d1555 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1726, d1555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro957 q selected
    | true =>
      simp only [d1726, d1555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1916 q = 2) : d1858 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1916, d1858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1916, d1858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1727 q = 2) : d1556 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1727, d1556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1727, d1556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1917 q = 2) : d1859 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1917, d1859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1917, d1859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1918 q = 2) : d1860 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1918, d1860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1918, d1860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15449 q = 2) : d15386 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15449, d15386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15449, d15386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15450 q = 2) : d15387 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15450, d15387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15450, d15387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10619 q selected
  have h9 (q : Pattern) (selected : d10200 q = 2) : d10063 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10200, d10063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10619 q selected
    | true =>
      simp only [d10200, d10063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15451 q = 2) : d15388 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15451, d15388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d15451, d15388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d10202 q = 2) : d10065 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10202, d10065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d10202, d10065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d15452 q = 2) : d15389 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15452, d15389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d15452, d15389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d15453 q = 2) : d15390 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15453, d15390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15453, d15390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d15454 q = 2) : d15391 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15454, d15391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d15454, d15391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d15455 q = 2) : d15392 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15455, d15392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15455, d15392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro14540 (p : Pattern) (selected : d15462 p = 2) : d15408 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1919 q = 2) : d1862 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1919, d1862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1919, d1862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro960 q selected
  have h2 (q : Pattern) (selected : d1741 q = 2) : d1570 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1741, d1570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro960 q selected
    | true =>
      simp only [d1741, d1570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1920 q = 2) : d1863 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1920, d1863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1920, d1863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1742 q = 2) : d1571 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1742, d1571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1742, d1571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1921 q = 2) : d1864 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1921, d1864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1921, d1864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1922 q = 2) : d1865 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1922, d1865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1922, d1865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15456 q = 2) : d15407 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15456, d15407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15456, d15407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15457 q = 2) : d15397 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15457, d15397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15457, d15397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10620 q selected
  have h9 (q : Pattern) (selected : d10215 q = 2) : d10085 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10215, d10085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10620 q selected
    | true =>
      simp only [d10215, d10085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15458 q = 2) : d15398 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15458, d15398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d15458, d15398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d10217 q = 2) : d10087 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10217, d10087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d10217, d10087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d15459 q = 2) : d15399 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15459, d15399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d15459, d15399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d15460 q = 2) : d15400 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15460, d15400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15460, d15400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d15461 q = 2) : d15401 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15461, d15401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d15461, d15401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d15462 q = 2) : d15408 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15462, d15408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15462, d15408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro14541 (p : Pattern) (selected : d15471 p = 2) : d15417 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13535 q = 2) : d6496 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13535, d6496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13535, d6496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10624 q selected
  have h2 (q : Pattern) (selected : d10243 q = 2) : d5134 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10243, d5134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10624 q selected
    | true =>
      simp only [d10243, d5134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13536 q = 2) : d6497 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13536, d6497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13536, d6497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10245 q = 2) : d5135 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10245, d5135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10245, d5135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13537 q = 2) : d6498 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13537, d6498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13537, d6498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13538 q = 2) : d6499 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13538, d6499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13538, d6499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13539 q = 2) : d6500 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13539, d6500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13539, d6500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15466 q = 2) : d15412 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15466, d15412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15466, d15412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10625 q selected
  have h9 (q : Pattern) (selected : d10255 q = 2) : d10135 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10255, d10135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10625 q selected
    | true =>
      simp only [d10255, d10135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15467 q = 2) : d15413 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15467, d15413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d15467, d15413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d10257 q = 2) : d10137 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10257, d10137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d10257, d10137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d15468 q = 2) : d15414 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15468, d15414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d15468, d15414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d15469 q = 2) : d15415 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15469, d15415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15469, d15415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d15470 q = 2) : d15416 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15470, d15416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d15470, d15416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d15471 q = 2) : d15417 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15471, d15417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15471, d15417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro14542 (p : Pattern) (selected : d15476 p = 2) : d15435 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1924 q = 2) : d1868 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1924, d1868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1924, d1868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro961 q selected
  have h2 (q : Pattern) (selected : d1753 q = 2) : d1582 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1753, d1582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro961 q selected
    | true =>
      simp only [d1753, d1582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1925 q = 2) : d1869 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1925, d1869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1925, d1869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1754 q = 2) : d1583 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1754, d1583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1754, d1583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1926 q = 2) : d1870 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1926, d1870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1926, d1870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1927 q = 2) : d1871 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1927, d1871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1927, d1871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1930 q = 2) : d1877 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1930, d1877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1930, d1877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15466 q = 2) : d15412 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15466, d15412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15466, d15412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10625 q selected
  have h9 (q : Pattern) (selected : d10255 q = 2) : d10135 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10255, d10135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10625 q selected
    | true =>
      simp only [d10255, d10135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15467 q = 2) : d15413 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15467, d15413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d15467, d15413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d10257 q = 2) : d10137 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10257, d10137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d10257, d10137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d15468 q = 2) : d15414 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15468, d15414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d15468, d15414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d15469 q = 2) : d15415 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15469, d15415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15469, d15415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d15470 q = 2) : d15416 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15470, d15416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d15470, d15416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d15476 q = 2) : d15435 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15476, d15435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15476, d15435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro14543 (p : Pattern) (selected : d15482 p = 2) : d163571 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15463 q = 2) : d15409 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15463, d15409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14539 q selected
    | true =>
      simp only [d15463, d15409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14540 q selected
  have h2 (q : Pattern) (selected : d15464 q = 2) : d15410 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15464, d15410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15464, d15410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15465 q = 2) : d15411 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15465, d15411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15465, d15411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d15472 q = 2) : d15418 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15472, d15418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14540 q selected
    | true =>
      simp only [d15472, d15418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14541 q selected
  have h5 (q : Pattern) (selected : d15473 q = 2) : d15419 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15473, d15419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15473, d15419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15474 q = 2) : d15420 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15474, d15420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15474, d15420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d15475 q = 2) : d15421 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15475, d15421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15475, d15421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d15477 q = 2) : d15436 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15477, d15436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14540 q selected
    | true =>
      simp only [d15477, d15436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14542 q selected
  have h9 (q : Pattern) (selected : d15478 q = 2) : d15437 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15478, d15437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15478, d15437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d15479 q = 2) : d15438 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15479, d15438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15479, d15438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d15480 q = 2) : d15439 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15480, d15439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d15480, d15439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d15481 q = 2) : d163570 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15481, d163570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15481, d163570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d15482 q = 2) : d163571 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15482, d163571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15482, d163571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro14544 (p : Pattern) (selected : d15486 p = 2) : d15441 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15477 q = 2) : d15436 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15477, d15436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14540 q selected
    | true =>
      simp only [d15477, d15436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14542 q selected
  have h2 (q : Pattern) (selected : d15478 q = 2) : d15437 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15478, d15437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15478, d15437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15479 q = 2) : d15438 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15479, d15438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15479, d15438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d15480 q = 2) : d15439 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15480, d15439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15480, d15439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15485 q = 2) : d15440 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15485, d15440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d15485, d15440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d15486 q = 2) : d15441 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15486, d15441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15486, d15441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14545 (p : Pattern) (selected : d15492 p = 2) : d163577 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15483 q = 2) : d163572 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15483, d163572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14543 q selected
    | true =>
      simp only [d15483, d163572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15484 q = 2) : d163573 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15484, d163573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15484, d163573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15487 q = 2) : d15442 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15487, d15442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14544 q selected
    | true =>
      simp only [d15487, d15442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15488 q = 2) : d15443 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15488, d15443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15488, d15443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d15489 q = 2) : d163574 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15489, d163574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15489, d163574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15490 q = 2) : d163575 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15490, d163575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15490, d163575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15491 q = 2) : d163576 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15491, d163576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15491, d163576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15492 q = 2) : d163577 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15492, d163577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15492, d163577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14546 (p : Pattern) (selected : d15496 p = 2) : d15521 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15487 q = 2) : d15442 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15487, d15442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14544 q selected
    | true =>
      simp only [d15487, d15442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15488 q = 2) : d15443 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15488, d15443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15488, d15443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15493 q = 2) : d15518 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15493, d15518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15493, d15518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15494 q = 2) : d15519 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15494, d15519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15494, d15519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15495 q = 2) : d15520 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15495, d15520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d15495, d15520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d15496 q = 2) : d15521 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15496, d15521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15496, d15521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14547 (p : Pattern) (selected : d15504 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15409 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14529 q selected
    | true =>
      simp only [d15409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14531 q selected
  have h2 (q : Pattern) (selected : d15410 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15411 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d15418 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14531 q selected
    | true =>
      simp only [d15418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14532 q selected
  have h5 (q : Pattern) (selected : d15419 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15420 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d15421 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d15499 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14531 q selected
    | true =>
      simp only [d15499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13629 q selected
  have h9 (q : Pattern) (selected : d15500 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d15501 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d15502 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d15502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d15503 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d15504 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro14548 (p : Pattern) (selected : d15510 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15505 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14547 q selected
    | true =>
      simp only [d15505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15506 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15507 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15508 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15509 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d15509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d15510 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14549 (p : Pattern) (selected : d15516 p = 2) : d163583 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15448 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14535 q selected
    | true =>
      simp only [d15448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14538 q selected
  have h2 (q : Pattern) (selected : d15497 q = 2) : d163578 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15497, d163578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14545 q selected
    | true =>
      simp only [d15497, d163578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14546 q selected
  have h3 (q : Pattern) (selected : d15498 q = 2) : d163579 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15498, d163579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d15498, d163579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d15511 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14548 q selected
    | true =>
      simp only [d15511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15512 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d15512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d15513 q = 2) : d163580 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15513, d163580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15513, d163580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d15514 q = 2) : d163581 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15514, d163581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15514, d163581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d15515 q = 2) : d163582 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15515, d163582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15515, d163582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d15516 q = 2) : d163583 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15516, d163583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15516, d163583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro14550 (p : Pattern) (selected : d15521 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15442 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14537 q selected
    | true =>
      simp only [d15442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15443 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15518 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15519 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15520 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d15520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d15521 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14551 (p : Pattern) (selected : d15527 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15522 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14550 q selected
    | true =>
      simp only [d15522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15523 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15524 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15525 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d15526 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15527 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14552 (p : Pattern) (selected : d15533 p = 2) : d163589 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15198 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14489 q selected
  have h2 (q : Pattern) (selected : d15199 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d15199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d15199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15208 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14489 q selected
    | true =>
      simp only [d15208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14492 q selected
  have h4 (q : Pattern) (selected : d15209 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d15209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15210 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d15210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15347 q = 2) : d15208 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15347, d15208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14513 q selected
    | true =>
      simp only [d15347, d15208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14523 q selected
  have h7 (q : Pattern) (selected : d15365 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14524 q selected
    | true =>
      simp only [d15365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14525 q selected
  have h8 (q : Pattern) (selected : d15366 q = 2) : d15209 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d15366, d15209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15366, d15209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d15367 q = 2) : d163562 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d15367, d163562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d15367, d163562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15368 q = 2) : d163563 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d15368, d163563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15368, d163563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d15372 q = 2) : d163565 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15372, d163565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15372, d163565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14526 q selected
  have h12 (q : Pattern) (selected : d15374 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14527 q selected
  have h13 (q : Pattern) (selected : d15375 q = 2) : d163566 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d15375, d163566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d15375, d163566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d15376 q = 2) : d163567 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d15376, d163567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d15376, d163567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d15377 q = 2) : d163568 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d15377, d163568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d15377, d163568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d15378 q = 2) : d163569 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d15378, d163569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d15378, d163569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d15517 q = 2) : d163584 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15517, d163584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15517, d163584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14549 q selected
  have h18 (q : Pattern) (selected : d15528 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14551 q selected
  have h19 (q : Pattern) (selected : d15529 q = 2) : d163585 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d15529, d163585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d15529, d163585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d15530 q = 2) : d163586 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d15530, d163586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d15530, d163586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d15531 q = 2) : d163587 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d15531, d163587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d15531, d163587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d15532 q = 2) : d163588 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d15532, d163588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d15532, d163588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d15533 q = 2) : d163589 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d15533, d163589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d15533, d163589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro14553 (p : Pattern) (selected : d15539 p = 2) : d163595 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15534 q = 2) : d163590 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d15534, d163590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15534, d163590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14552 q selected
  have h2 (q : Pattern) (selected : d15535 q = 2) : d163591 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d15535, d163591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15535, d163591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15536 q = 2) : d163592 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d15536, d163592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15536, d163592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d15537 q = 2) : d163593 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d15537, d163593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15537, d163593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d15538 q = 2) : d163594 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d15538, d163594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15538, d163594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15539 q = 2) : d163595 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d15539, d163595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15539, d163595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14554 (p : Pattern) (selected : d15546 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2035 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1011 q selected
    | true =>
      simp only [d2035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2036 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2037 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2038 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15544 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d15544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10353 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10641 q selected
    | true =>
      simp only [d10353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10355 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13675 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d13676 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d13676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15545 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d15545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d15546 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14555 (p : Pattern) (selected : d15551 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2053 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1016 q selected
    | true =>
      simp only [d2053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2054 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2055 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2056 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15547 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d15547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10371 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10644 q selected
    | true =>
      simp only [d10371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10373 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15548 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d15549 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d15549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15550 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d15550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d15551 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14556 (p : Pattern) (selected : d15558 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d5247 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3872 q selected
    | true =>
      simp only [d5247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d5248 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d5248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d5249 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d5250 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d5250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d5251 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d5251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10412 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10649 q selected
    | true =>
      simp only [d10412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10414 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15555 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d15556 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d15556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15557 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d15557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d15558 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14557 (p : Pattern) (selected : d15563 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2065 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1017 q selected
    | true =>
      simp only [d2065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2066 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2067 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2068 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2071 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10412 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10649 q selected
    | true =>
      simp only [d10412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10414 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15555 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d15556 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d15556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15557 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d15557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d15563 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14558 (p : Pattern) (selected : d15569 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15552 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14554 q selected
    | true =>
      simp only [d15552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14555 q selected
  have h2 (q : Pattern) (selected : d15553 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15554 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d15559 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14555 q selected
    | true =>
      simp only [d15559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14556 q selected
  have h5 (q : Pattern) (selected : d15560 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15561 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d15562 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d15564 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14555 q selected
    | true =>
      simp only [d15564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14557 q selected
  have h9 (q : Pattern) (selected : d15565 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d15566 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d15567 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d15567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d15568 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d15569 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro14559 (p : Pattern) (selected : d15573 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15564 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14555 q selected
    | true =>
      simp only [d15564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14557 q selected
  have h2 (q : Pattern) (selected : d15565 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15566 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d15567 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15572 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d15572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d15573 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14560 (p : Pattern) (selected : d15579 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15570 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14558 q selected
    | true =>
      simp only [d15570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15571 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15574 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14559 q selected
    | true =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15575 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d15576 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15577 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15578 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15579 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14561 (p : Pattern) (selected : d15583 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15574 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14559 q selected
    | true =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15575 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15580 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15581 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15582 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d15582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d15583 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14562 (p : Pattern) (selected : d15589 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15584 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14560 q selected
    | true =>
      simp only [d15584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14561 q selected
  have h2 (q : Pattern) (selected : d15585 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15586 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15587 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d15588 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15589 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14563 (p : Pattern) (selected : d15592 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15570 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14558 q selected
    | true =>
      simp only [d15570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15571 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15574 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14559 q selected
    | true =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15575 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d15576 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15577 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15578 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15592 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14564 (p : Pattern) (selected : d15593 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15574 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14559 q selected
    | true =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15575 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15580 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15581 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15582 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d15582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d15593 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14565 (p : Pattern) (selected : d15599 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15584 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14560 q selected
    | true =>
      simp only [d15584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14561 q selected
  have h2 (q : Pattern) (selected : d15585 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15586 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15587 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d15588 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15594 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14563 q selected
    | true =>
      simp only [d15594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14564 q selected
  have h7 (q : Pattern) (selected : d15595 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d15596 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d15597 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d15598 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d15599 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14566 (p : Pattern) (selected : d15604 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15570 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14558 q selected
    | true =>
      simp only [d15570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15571 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15574 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14559 q selected
    | true =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15575 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d15576 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15577 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15603 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d15604 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14567 (p : Pattern) (selected : d15606 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15574 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14559 q selected
    | true =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15575 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15580 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15581 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15605 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15606 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14568 (p : Pattern) (selected : d15613 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15570 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14558 q selected
    | true =>
      simp only [d15570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15571 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15574 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14559 q selected
    | true =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15575 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d15576 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15611 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d15612 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15613 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14569 (p : Pattern) (selected : d15616 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15574 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14559 q selected
    | true =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15575 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15580 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15614 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d15615 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d15615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d15616 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14570 (p : Pattern) (selected : d15621 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2144 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1034 q selected
    | true =>
      simp only [d2144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2145 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2146 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2147 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15620 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d15620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d15621 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14571 (p : Pattern) (selected : d15625 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d10353 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10641 q selected
    | true =>
      simp only [d10353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10355 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13675 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13676 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15545 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d15545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10371 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10644 q selected
    | true =>
      simp only [d10371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10373 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15548 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d15549 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d15549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15550 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d15550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d15625 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14572 (p : Pattern) (selected : d15631 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15622 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14570 q selected
    | true =>
      simp only [d15622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14554 q selected
  have h2 (q : Pattern) (selected : d15623 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15624 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d15626 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14554 q selected
    | true =>
      simp only [d15626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14571 q selected
  have h5 (q : Pattern) (selected : d15627 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15628 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d15629 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d15552 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14554 q selected
    | true =>
      simp only [d15552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14555 q selected
  have h9 (q : Pattern) (selected : d15553 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d15554 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d15559 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14555 q selected
    | true =>
      simp only [d15559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14556 q selected
  have h12 (q : Pattern) (selected : d15560 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d15561 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d15562 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d15562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d15630 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d15631 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d15631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro14573 (p : Pattern) (selected : d15636 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15552 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14554 q selected
    | true =>
      simp only [d15552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14555 q selected
  have h2 (q : Pattern) (selected : d15553 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15554 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d15559 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14555 q selected
    | true =>
      simp only [d15559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14556 q selected
  have h5 (q : Pattern) (selected : d15560 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15561 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d15562 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d15634 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d15635 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d15636 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d15636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro14574 (p : Pattern) (selected : d15642 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15632 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14572 q selected
    | true =>
      simp only [d15632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15633 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15637 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14573 q selected
    | true =>
      simp only [d15637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15638 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d15639 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15640 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15641 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15642 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14575 (p : Pattern) (selected : d15646 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15637 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14573 q selected
    | true =>
      simp only [d15637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15638 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15574 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14559 q selected
    | true =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15575 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d15643 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15644 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15645 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15646 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14576 (p : Pattern) (selected : d15652 p = 2) : d15546 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2201 q = 2) : d2035 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2201, d2035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1045 q selected
    | true =>
      simp only [d2201, d2035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2202 q = 2) : d2036 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2202, d2036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2202, d2036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2203 q = 2) : d2037 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2203, d2037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2203, d2037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2204 q = 2) : d2038 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2204, d2038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2204, d2038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15648 q = 2) : d15544 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15648, d15544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d15648, d15544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10468 q = 2) : d10353 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10468, d10353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10658 q selected
    | true =>
      simp only [d10468, d10353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10470 q = 2) : d10355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10470, d10355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10470, d10355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15649 q = 2) : d13675 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15649, d13675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15649, d13675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d15650 q = 2) : d13676 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15650, d13676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d15650, d13676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15651 q = 2) : d15545 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15651, d15545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d15651, d15545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d15652 q = 2) : d15546 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15652, d15546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15652, d15546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14577 (p : Pattern) (selected : d15657 p = 2) : d15551 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2219 q = 2) : d2053 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2219, d2053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1050 q selected
    | true =>
      simp only [d2219, d2053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2220 q = 2) : d2054 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2220, d2054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2220, d2054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2221 q = 2) : d2055 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2221, d2055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2221, d2055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2222 q = 2) : d2056 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2222, d2056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2222, d2056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15653 q = 2) : d15547 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15653, d15547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d15653, d15547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10482 q = 2) : d10371 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10482, d10371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10659 q selected
    | true =>
      simp only [d10482, d10371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10484 q = 2) : d10373 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10484, d10373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10484, d10373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15654 q = 2) : d15548 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15654, d15548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15654, d15548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d15655 q = 2) : d15549 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15655, d15549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d15655, d15549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15656 q = 2) : d15550 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15656, d15550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d15656, d15550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d15657 q = 2) : d15551 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15657, d15551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15657, d15551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14578 (p : Pattern) (selected : d15664 p = 2) : d15558 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d10508 q = 2) : d5247 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10508, d5247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10663 q selected
    | true =>
      simp only [d10508, d5247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10510 q = 2) : d5248 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10510, d5248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10510, d5248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13710 q = 2) : d5249 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13710, d5249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13710, d5249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13711 q = 2) : d5250 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13711, d5250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13711, d5250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13712 q = 2) : d5251 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13712, d5251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13712, d5251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
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
  have h11 (q : Pattern) (selected : d15664 q = 2) : d15558 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15664, d15558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15664, d15558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14579 (p : Pattern) (selected : d15669 p = 2) : d15563 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2231 q = 2) : d2065 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2231, d2065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1051 q selected
    | true =>
      simp only [d2231, d2065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2232 q = 2) : d2066 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2232, d2066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2232, d2066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2233 q = 2) : d2067 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2233, d2067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2233, d2067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2234 q = 2) : d2068 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2234, d2068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2234, d2068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2237 q = 2) : d2071 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2237, d2071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2237, d2071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
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
  have h11 (q : Pattern) (selected : d15669 q = 2) : d15563 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15669, d15563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15669, d15563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14580 (p : Pattern) (selected : d15675 p = 2) : d15569 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15658 q = 2) : d15552 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15658, d15552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14576 q selected
    | true =>
      simp only [d15658, d15552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14577 q selected
  have h2 (q : Pattern) (selected : d15659 q = 2) : d15553 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15659, d15553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15659, d15553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15660 q = 2) : d15554 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15660, d15554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15660, d15554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d15665 q = 2) : d15559 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15665, d15559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14577 q selected
    | true =>
      simp only [d15665, d15559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14578 q selected
  have h5 (q : Pattern) (selected : d15666 q = 2) : d15560 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15666, d15560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15666, d15560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15667 q = 2) : d15561 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15667, d15561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15667, d15561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d15668 q = 2) : d15562 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15668, d15562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15668, d15562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d15670 q = 2) : d15564 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15670, d15564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14577 q selected
    | true =>
      simp only [d15670, d15564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14579 q selected
  have h9 (q : Pattern) (selected : d15671 q = 2) : d15565 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15671, d15565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15671, d15565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d15672 q = 2) : d15566 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15672, d15566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15672, d15566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d15673 q = 2) : d15567 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15673, d15567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d15673, d15567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d15674 q = 2) : d15568 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15674, d15568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15674, d15568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d15675 q = 2) : d15569 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15675, d15569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15675, d15569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro14581 (p : Pattern) (selected : d15679 p = 2) : d15573 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15670 q = 2) : d15564 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15670, d15564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14577 q selected
    | true =>
      simp only [d15670, d15564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14579 q selected
  have h2 (q : Pattern) (selected : d15671 q = 2) : d15565 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15671, d15565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15671, d15565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15672 q = 2) : d15566 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15672, d15566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15672, d15566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d15673 q = 2) : d15567 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15673, d15567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15673, d15567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15678 q = 2) : d15572 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15678, d15572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d15678, d15572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d15679 q = 2) : d15573 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15679, d15573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15679, d15573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14582 (p : Pattern) (selected : d15685 p = 2) : d15579 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15676 q = 2) : d15570 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15676, d15570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14580 q selected
    | true =>
      simp only [d15676, d15570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15677 q = 2) : d15571 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15677, d15571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15677, d15571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15680 q = 2) : d15574 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15680, d15574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14581 q selected
    | true =>
      simp only [d15680, d15574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15681 q = 2) : d15575 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15681, d15575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15681, d15575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d15682 q = 2) : d15576 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15682, d15576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15682, d15576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15683 q = 2) : d15577 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15683, d15577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15683, d15577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15684 q = 2) : d15578 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15684, d15578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15684, d15578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15685 q = 2) : d15579 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15685, d15579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15685, d15579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14583 (p : Pattern) (selected : d15689 p = 2) : d15583 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15680 q = 2) : d15574 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15680, d15574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14581 q selected
    | true =>
      simp only [d15680, d15574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15681 q = 2) : d15575 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15681, d15575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15681, d15575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15686 q = 2) : d15580 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15686, d15580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15686, d15580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15687 q = 2) : d15581 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15687, d15581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15687, d15581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15688 q = 2) : d15582 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15688, d15582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d15688, d15582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d15689 q = 2) : d15583 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15689, d15583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15689, d15583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14584 (p : Pattern) (selected : d15697 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15552 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14554 q selected
    | true =>
      simp only [d15552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14555 q selected
  have h2 (q : Pattern) (selected : d15553 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15554 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d15559 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14555 q selected
    | true =>
      simp only [d15559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14556 q selected
  have h5 (q : Pattern) (selected : d15560 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15561 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d15562 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d15692 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14555 q selected
    | true =>
      simp only [d15692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13648 q selected
  have h9 (q : Pattern) (selected : d15693 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d15694 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d15695 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d15695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d15696 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d15697 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro14585 (p : Pattern) (selected : d15703 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15698 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14584 q selected
    | true =>
      simp only [d15698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15699 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15700 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15701 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15702 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d15702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d15703 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14586 (p : Pattern) (selected : d15709 p = 2) : d15589 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15607 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14566 q selected
    | true =>
      simp only [d15607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14567 q selected
  have h2 (q : Pattern) (selected : d15608 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15609 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15610 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d15617 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14568 q selected
    | true =>
      simp only [d15617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14569 q selected
  have h6 (q : Pattern) (selected : d15618 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d15619 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15647 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14574 q selected
    | true =>
      simp only [d15647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14575 q selected
  have h9 (q : Pattern) (selected : d15690 q = 2) : d15584 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15690, d15584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14582 q selected
    | true =>
      simp only [d15690, d15584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14583 q selected
  have h10 (q : Pattern) (selected : d15691 q = 2) : d15585 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15691, d15585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d15691, d15585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d15704 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14585 q selected
    | true =>
      simp only [d15704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d15705 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d15705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d15706 q = 2) : d15586 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15706, d15586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d15706, d15586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d15707 q = 2) : d15587 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15707, d15587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15707, d15587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d15708 q = 2) : d15588 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15708, d15588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d15708, d15588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d15709 q = 2) : d15589 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15709, d15589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15709, d15589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro14587 (p : Pattern) (selected : d15710 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15570 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14558 q selected
    | true =>
      simp only [d15570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15571 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15574 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14559 q selected
    | true =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15575 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d15576 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15577 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15603 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d15710 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14588 (p : Pattern) (selected : d15711 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15574 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14559 q selected
    | true =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15575 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15580 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15581 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15605 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15711 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14589 (p : Pattern) (selected : d15716 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15570 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14558 q selected
    | true =>
      simp only [d15570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15571 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15574 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14559 q selected
    | true =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15575 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d15576 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15611 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d15612 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15716 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14590 (p : Pattern) (selected : d15717 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15574 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14559 q selected
    | true =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15575 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15580 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15614 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d15615 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d15615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d15717 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14591 (p : Pattern) (selected : d15721 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15632 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14572 q selected
    | true =>
      simp only [d15632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15633 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15637 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14573 q selected
    | true =>
      simp only [d15637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15638 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d15639 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15640 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15641 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15721 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14592 (p : Pattern) (selected : d15722 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15637 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14573 q selected
    | true =>
      simp only [d15637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15638 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15574 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14559 q selected
    | true =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15575 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d15643 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15644 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15645 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15722 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14593 (p : Pattern) (selected : d15724 p = 2) : d15592 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15676 q = 2) : d15570 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15676, d15570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14580 q selected
    | true =>
      simp only [d15676, d15570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15677 q = 2) : d15571 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15677, d15571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15677, d15571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15680 q = 2) : d15574 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15680, d15574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14581 q selected
    | true =>
      simp only [d15680, d15574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15681 q = 2) : d15575 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15681, d15575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15681, d15575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d15682 q = 2) : d15576 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15682, d15576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15682, d15576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15683 q = 2) : d15577 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15683, d15577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15683, d15577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15684 q = 2) : d15578 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15684, d15578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15684, d15578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15724 q = 2) : d15592 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15724, d15592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15724, d15592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14594 (p : Pattern) (selected : d15725 p = 2) : d15593 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15680 q = 2) : d15574 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15680, d15574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14581 q selected
    | true =>
      simp only [d15680, d15574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15681 q = 2) : d15575 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15681, d15575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15681, d15575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15686 q = 2) : d15580 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15686, d15580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15686, d15580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15687 q = 2) : d15581 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15687, d15581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15687, d15581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15688 q = 2) : d15582 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15688, d15582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d15688, d15582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d15725 q = 2) : d15593 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15725, d15593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15725, d15593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14595 (p : Pattern) (selected : d15728 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15698 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14584 q selected
    | true =>
      simp only [d15698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15699 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15700 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15701 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15702 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d15702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d15728 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14596 (p : Pattern) (selected : d15734 p = 2) : d15599 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15607 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14566 q selected
    | true =>
      simp only [d15607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14567 q selected
  have h2 (q : Pattern) (selected : d15608 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15609 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15610 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d15617 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14568 q selected
    | true =>
      simp only [d15617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14569 q selected
  have h6 (q : Pattern) (selected : d15618 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d15619 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15647 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14574 q selected
    | true =>
      simp only [d15647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14575 q selected
  have h9 (q : Pattern) (selected : d15690 q = 2) : d15584 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15690, d15584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14582 q selected
    | true =>
      simp only [d15690, d15584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14583 q selected
  have h10 (q : Pattern) (selected : d15691 q = 2) : d15585 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15691, d15585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d15691, d15585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d15704 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14585 q selected
    | true =>
      simp only [d15704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d15705 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d15705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d15706 q = 2) : d15586 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15706, d15586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d15706, d15586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d15707 q = 2) : d15587 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15707, d15587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15707, d15587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d15708 q = 2) : d15588 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15708, d15588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d15708, d15588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d15712 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14587 q selected
    | true =>
      simp only [d15712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14588 q selected
  have h17 (q : Pattern) (selected : d15713 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d15714 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d15714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d15715 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d15718 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14589 q selected
    | true =>
      simp only [d15718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14590 q selected
  have h21 (q : Pattern) (selected : d15719 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d15720 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d15720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d15723 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14591 q selected
    | true =>
      simp only [d15723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14592 q selected
  have h24 (q : Pattern) (selected : d15726 q = 2) : d15594 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15726, d15594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14593 q selected
    | true =>
      simp only [d15726, d15594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14594 q selected
  have h25 (q : Pattern) (selected : d15727 q = 2) : d15595 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15727, d15595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d15727, d15595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d15729 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14595 q selected
    | true =>
      simp only [d15729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d15730 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d15730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d15731 q = 2) : d15596 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15731, d15596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d15731, d15596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d15732 q = 2) : d15597 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15732, d15597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d15732, d15597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d15733 q = 2) : d15598 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15733, d15598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d15733, d15598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d15734 q = 2) : d15599 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15734, d15599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d15734, d15599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro14597 (p : Pattern) (selected : d15746 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15736 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14575 q selected
    | true =>
      simp only [d15736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14561 q selected
  have h2 (q : Pattern) (selected : d15737 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15738 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15739 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d15740 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15741 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14561 q selected
    | true =>
      simp only [d15741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15742 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d15743 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d15744 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d15745 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d15746 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14598 (p : Pattern) (selected : d15752 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15741 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14561 q selected
    | true =>
      simp only [d15741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15742 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15743 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15744 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d15745 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15747 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14564 q selected
    | true =>
      simp only [d15747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15748 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d15749 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d15750 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d15751 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d15752 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14599 (p : Pattern) (selected : d15759 p = 2) : d163602 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15723 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14591 q selected
    | true =>
      simp only [d15723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14592 q selected
  have h2 (q : Pattern) (selected : d15726 q = 2) : d15594 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15726, d15594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14593 q selected
    | true =>
      simp only [d15726, d15594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14594 q selected
  have h3 (q : Pattern) (selected : d15727 q = 2) : d15595 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15727, d15595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d15727, d15595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d15729 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14595 q selected
    | true =>
      simp only [d15729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15730 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d15730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d15731 q = 2) : d15596 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15731, d15596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15731, d15596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d15757 q = 2) : d15597 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15757, d15597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15757, d15597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d15758 q = 2) : d15598 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15758, d15598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15758, d15598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d15759 q = 2) : d163602 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15759, d163602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15759, d163602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro14600 (p : Pattern) (selected : d15761 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15747 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14564 q selected
    | true =>
      simp only [d15747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15748 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15749 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15750 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d15751 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15761 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14601 (p : Pattern) (selected : d15768 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2331 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1034 q selected
  have h2 (q : Pattern) (selected : d2144 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1034 q selected
    | true =>
      simp only [d2144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2332 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2145 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2333 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2334 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15767 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15768 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14602 (p : Pattern) (selected : d15771 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2335 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1011 q selected
  have h2 (q : Pattern) (selected : d2035 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1011 q selected
    | true =>
      simp only [d2035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2336 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2036 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2337 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2338 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15769 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13813 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10641 q selected
  have h9 (q : Pattern) (selected : d10353 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10641 q selected
    | true =>
      simp only [d10353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d13814 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d13814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d10355 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d10355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d13815 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d13815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d13816 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d13816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d15770 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d15770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d15771 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro14603 (p : Pattern) (selected : d15780 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13813 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10641 q selected
  have h2 (q : Pattern) (selected : d10353 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10641 q selected
    | true =>
      simp only [d10353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13814 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10355 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13815 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13816 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15770 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15775 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10644 q selected
  have h9 (q : Pattern) (selected : d10371 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10644 q selected
    | true =>
      simp only [d10371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15776 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d15776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d10373 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d10373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d15777 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d15777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d15778 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d15779 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d15779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d15780 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro14604 (p : Pattern) (selected : d15786 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2340 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1016 q selected
  have h2 (q : Pattern) (selected : d2053 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1016 q selected
    | true =>
      simp only [d2053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2341 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2054 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2342 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2343 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15785 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15775 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10644 q selected
  have h9 (q : Pattern) (selected : d10371 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10644 q selected
    | true =>
      simp only [d10371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15776 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d15776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d10373 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d10373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d15777 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d15777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d15778 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d15779 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d15779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d15786 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro14605 (p : Pattern) (selected : d15795 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d6643 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d6643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3872 q selected
  have h2 (q : Pattern) (selected : d5247 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3872 q selected
    | true =>
      simp only [d5247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d6644 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d6644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d6644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d5248 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d5248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d6645 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d6645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d6645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d6646 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d6646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d6646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d6647 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d6647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d6647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
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
  have h15 (q : Pattern) (selected : d15795 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro14606 (p : Pattern) (selected : d15801 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15772 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14601 q selected
    | true =>
      simp only [d15772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14602 q selected
  have h2 (q : Pattern) (selected : d15773 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15774 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d15781 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14602 q selected
    | true =>
      simp only [d15781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14603 q selected
  have h5 (q : Pattern) (selected : d15782 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15783 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d15784 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d15787 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14602 q selected
    | true =>
      simp only [d15787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14604 q selected
  have h9 (q : Pattern) (selected : d15788 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d15789 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d15796 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14604 q selected
    | true =>
      simp only [d15796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14605 q selected
  have h12 (q : Pattern) (selected : d15797 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d15798 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d15799 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d15799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d15800 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d15801 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d15801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro14607 (p : Pattern) (selected : d15806 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15787 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14602 q selected
    | true =>
      simp only [d15787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14604 q selected
  have h2 (q : Pattern) (selected : d15788 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15789 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d15796 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14604 q selected
    | true =>
      simp only [d15796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14605 q selected
  have h5 (q : Pattern) (selected : d15797 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15798 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d15799 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d15804 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d15805 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d15806 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d15806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro14608 (p : Pattern) (selected : d15812 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15802 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14606 q selected
    | true =>
      simp only [d15802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15803 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15807 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14607 q selected
    | true =>
      simp only [d15807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15808 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d15809 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15810 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15811 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15812 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14609 (p : Pattern) (selected : d15813 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2346 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1017 q selected
  have h2 (q : Pattern) (selected : d2065 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1017 q selected
    | true =>
      simp only [d2065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2347 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2066 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2348 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2349 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d2355 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d2355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
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
  have h15 (q : Pattern) (selected : d15813 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro14610 (p : Pattern) (selected : d15819 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15814 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14604 q selected
    | true =>
      simp only [d15814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14609 q selected
  have h2 (q : Pattern) (selected : d15815 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15816 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d15817 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15818 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d15818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d15819 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14611 (p : Pattern) (selected : d15825 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15807 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14607 q selected
    | true =>
      simp only [d15807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15808 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15820 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14610 q selected
    | true =>
      simp only [d15820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15821 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d15822 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15823 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15824 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15825 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14612 (p : Pattern) (selected : d15833 p = 2) : d15771 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2393 q = 2) : d2335 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2393, d2335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2393, d2335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1045 q selected
  have h2 (q : Pattern) (selected : d2201 q = 2) : d2035 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2201, d2035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1045 q selected
    | true =>
      simp only [d2201, d2035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2394 q = 2) : d2336 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2394, d2336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2394, d2336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2202 q = 2) : d2036 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2202, d2036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2202, d2036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2395 q = 2) : d2337 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2395, d2337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2395, d2337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2396 q = 2) : d2338 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2396, d2338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2396, d2338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15827 q = 2) : d15769 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15827, d15769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15827, d15769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15828 q = 2) : d13813 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15828, d13813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15828, d13813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10658 q selected
  have h9 (q : Pattern) (selected : d10468 q = 2) : d10353 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10468, d10353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10658 q selected
    | true =>
      simp only [d10468, d10353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15829 q = 2) : d13814 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15829, d13814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d15829, d13814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d10470 q = 2) : d10355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10470, d10355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d10470, d10355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d15830 q = 2) : d13815 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15830, d13815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d15830, d13815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d15831 q = 2) : d13816 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15831, d13816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15831, d13816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d15832 q = 2) : d15770 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15832, d15770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d15832, d15770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d15833 q = 2) : d15771 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15833, d15771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15833, d15771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro14613 (p : Pattern) (selected : d15840 p = 2) : d15786 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2397 q = 2) : d2340 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2397, d2340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2397, d2340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1050 q selected
  have h2 (q : Pattern) (selected : d2219 q = 2) : d2053 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2219, d2053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1050 q selected
    | true =>
      simp only [d2219, d2053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2398 q = 2) : d2341 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2398, d2341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2398, d2341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2220 q = 2) : d2054 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2220, d2054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2220, d2054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2399 q = 2) : d2342 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2399, d2342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2399, d2342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2400 q = 2) : d2343 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2400, d2343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2400, d2343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15834 q = 2) : d15785 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15834, d15785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15834, d15785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15835 q = 2) : d15775 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15835, d15775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15835, d15775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10659 q selected
  have h9 (q : Pattern) (selected : d10482 q = 2) : d10371 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10482, d10371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10659 q selected
    | true =>
      simp only [d10482, d10371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15836 q = 2) : d15776 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15836, d15776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d15836, d15776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d10484 q = 2) : d10373 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10484, d10373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d10484, d10373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d15837 q = 2) : d15777 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15837, d15777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d15837, d15777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d15838 q = 2) : d15778 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15838, d15778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15838, d15778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d15839 q = 2) : d15779 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15839, d15779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d15839, d15779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d15840 q = 2) : d15786 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15840, d15786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15840, d15786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro14614 (p : Pattern) (selected : d15849 p = 2) : d15795 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13862 q = 2) : d6643 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13862, d6643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13862, d6643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10663 q selected
  have h2 (q : Pattern) (selected : d10508 q = 2) : d5247 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10508, d5247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10663 q selected
    | true =>
      simp only [d10508, d5247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13863 q = 2) : d6644 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13863, d6644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13863, d6644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10510 q = 2) : d5248 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10510, d5248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10510, d5248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13864 q = 2) : d6645 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13864, d6645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13864, d6645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13865 q = 2) : d6646 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13865, d6646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13865, d6646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13866 q = 2) : d6647 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13866, d6647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13866, d6647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
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
  have h15 (q : Pattern) (selected : d15849 q = 2) : d15795 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15849, d15795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15849, d15795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro14615 (p : Pattern) (selected : d15854 p = 2) : d15813 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2402 q = 2) : d2346 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2402, d2346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2402, d2346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1051 q selected
  have h2 (q : Pattern) (selected : d2231 q = 2) : d2065 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2231, d2065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1051 q selected
    | true =>
      simp only [d2231, d2065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2403 q = 2) : d2347 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2403, d2347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2403, d2347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2232 q = 2) : d2066 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2232, d2066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2232, d2066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2404 q = 2) : d2348 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2404, d2348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2404, d2348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2405 q = 2) : d2349 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2405, d2349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2405, d2349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d2408 q = 2) : d2355 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2408, d2355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d2408, d2355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
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
  have h15 (q : Pattern) (selected : d15854 q = 2) : d15813 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15854, d15813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15854, d15813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro14616 (p : Pattern) (selected : d15860 p = 2) : d163609 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15841 q = 2) : d15787 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15841, d15787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14612 q selected
    | true =>
      simp only [d15841, d15787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14613 q selected
  have h2 (q : Pattern) (selected : d15842 q = 2) : d15788 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15842, d15788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15842, d15788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15843 q = 2) : d15789 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15843, d15789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15843, d15789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d15850 q = 2) : d15796 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15850, d15796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14613 q selected
    | true =>
      simp only [d15850, d15796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14614 q selected
  have h5 (q : Pattern) (selected : d15851 q = 2) : d15797 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15851, d15797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15851, d15797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15852 q = 2) : d15798 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15852, d15798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15852, d15798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d15853 q = 2) : d15799 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15853, d15799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15853, d15799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d15855 q = 2) : d15814 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15855, d15814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14613 q selected
    | true =>
      simp only [d15855, d15814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14615 q selected
  have h9 (q : Pattern) (selected : d15856 q = 2) : d15815 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15856, d15815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15856, d15815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d15857 q = 2) : d15816 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15857, d15816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15857, d15816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d15858 q = 2) : d15817 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15858, d15817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d15858, d15817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d15859 q = 2) : d163608 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15859, d163608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15859, d163608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d15860 q = 2) : d163609 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15860, d163609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15860, d163609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro14617 (p : Pattern) (selected : d15864 p = 2) : d15819 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15855 q = 2) : d15814 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15855, d15814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14613 q selected
    | true =>
      simp only [d15855, d15814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14615 q selected
  have h2 (q : Pattern) (selected : d15856 q = 2) : d15815 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15856, d15815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15856, d15815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15857 q = 2) : d15816 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15857, d15816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15857, d15816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d15858 q = 2) : d15817 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15858, d15817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15858, d15817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15863 q = 2) : d15818 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15863, d15818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d15863, d15818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d15864 q = 2) : d15819 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15864, d15819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15864, d15819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14618 (p : Pattern) (selected : d15870 p = 2) : d163615 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15861 q = 2) : d163610 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15861, d163610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14616 q selected
    | true =>
      simp only [d15861, d163610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15862 q = 2) : d163611 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15862, d163611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15862, d163611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15865 q = 2) : d15820 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15865, d15820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14617 q selected
    | true =>
      simp only [d15865, d15820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15866 q = 2) : d15821 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15866, d15821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15866, d15821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d15867 q = 2) : d163612 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15867, d163612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15867, d163612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15868 q = 2) : d163613 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15868, d163613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15868, d163613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15869 q = 2) : d163614 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15869, d163614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15869, d163614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15870 q = 2) : d163615 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15870, d163615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15870, d163615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14619 (p : Pattern) (selected : d15874 p = 2) : d15899 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15865 q = 2) : d15820 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15865, d15820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14617 q selected
    | true =>
      simp only [d15865, d15820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15866 q = 2) : d15821 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15866, d15821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15866, d15821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15871 q = 2) : d15896 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15871, d15896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15871, d15896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15872 q = 2) : d15897 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15872, d15897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15872, d15897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15873 q = 2) : d15898 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15873, d15898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d15873, d15898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d15874 q = 2) : d15899 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15874, d15899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15874, d15899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14620 (p : Pattern) (selected : d15882 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15787 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14602 q selected
    | true =>
      simp only [d15787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14604 q selected
  have h2 (q : Pattern) (selected : d15788 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15789 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d15796 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14604 q selected
    | true =>
      simp only [d15796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14605 q selected
  have h5 (q : Pattern) (selected : d15797 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15798 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d15799 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d15877 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14604 q selected
    | true =>
      simp only [d15877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13698 q selected
  have h9 (q : Pattern) (selected : d15878 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d15879 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d15880 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d15880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d15881 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d15882 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro14621 (p : Pattern) (selected : d15888 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15883 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14620 q selected
    | true =>
      simp only [d15883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15884 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15885 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15886 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15887 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d15887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d15888 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14622 (p : Pattern) (selected : d15894 p = 2) : d163621 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15826 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14608 q selected
    | true =>
      simp only [d15826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14611 q selected
  have h2 (q : Pattern) (selected : d15875 q = 2) : d163616 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15875, d163616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14618 q selected
    | true =>
      simp only [d15875, d163616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14619 q selected
  have h3 (q : Pattern) (selected : d15876 q = 2) : d163617 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15876, d163617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d15876, d163617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d15889 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14621 q selected
    | true =>
      simp only [d15889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15890 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d15890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d15891 q = 2) : d163618 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15891, d163618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15891, d163618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d15892 q = 2) : d163619 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15892, d163619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15892, d163619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d15893 q = 2) : d163620 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15893, d163620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15893, d163620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d15894 q = 2) : d163621 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15894, d163621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15894, d163621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro14623 (p : Pattern) (selected : d15899 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15820 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14610 q selected
    | true =>
      simp only [d15820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15821 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15896 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15897 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15898 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d15898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d15899 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14624 (p : Pattern) (selected : d15905 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15900 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14623 q selected
    | true =>
      simp only [d15900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15901 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15902 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15903 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d15904 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15905 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14625 (p : Pattern) (selected : d15911 p = 2) : d163627 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15590 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14562 q selected
  have h2 (q : Pattern) (selected : d15591 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d15591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d15591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15600 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14562 q selected
    | true =>
      simp only [d15600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14565 q selected
  have h4 (q : Pattern) (selected : d15601 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d15601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15602 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d15602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15735 q = 2) : d15600 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15735, d15600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14586 q selected
    | true =>
      simp only [d15735, d15600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14596 q selected
  have h7 (q : Pattern) (selected : d15753 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14597 q selected
    | true =>
      simp only [d15753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14598 q selected
  have h8 (q : Pattern) (selected : d15754 q = 2) : d15601 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d15754, d15601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15754, d15601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d15755 q = 2) : d163600 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d15755, d163600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d15755, d163600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15756 q = 2) : d163601 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d15756, d163601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15756, d163601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d15760 q = 2) : d163603 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15760, d163603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15760, d163603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14599 q selected
  have h12 (q : Pattern) (selected : d15762 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14600 q selected
  have h13 (q : Pattern) (selected : d15763 q = 2) : d163604 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d15763, d163604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d15763, d163604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d15764 q = 2) : d163605 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d15764, d163605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d15764, d163605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d15765 q = 2) : d163606 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d15765, d163606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d15765, d163606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d15766 q = 2) : d163607 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d15766, d163607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d15766, d163607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d15895 q = 2) : d163622 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15895, d163622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15895, d163622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14622 q selected
  have h18 (q : Pattern) (selected : d15906 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14624 q selected
  have h19 (q : Pattern) (selected : d15907 q = 2) : d163623 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d15907, d163623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d15907, d163623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d15908 q = 2) : d163624 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d15908, d163624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d15908, d163624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d15909 q = 2) : d163625 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d15909, d163625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d15909, d163625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d15910 q = 2) : d163626 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d15910, d163626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d15910, d163626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d15911 q = 2) : d163627 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d15911, d163627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d15911, d163627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro14626 (p : Pattern) (selected : d15917 p = 2) : d163633 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15912 q = 2) : d163628 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d15912, d163628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15912, d163628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14625 q selected
  have h2 (q : Pattern) (selected : d15913 q = 2) : d163629 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d15913, d163629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15913, d163629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d15914 q = 2) : d163630 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d15914, d163630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15914, d163630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d15915 q = 2) : d163631 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d15915, d163631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15915, d163631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d15916 q = 2) : d163632 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d15916, d163632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15916, d163632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15917 q = 2) : d163633 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d15917, d163633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15917, d163633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14627 (p : Pattern) (selected : d15923 p = 2) : d163639 p = 1 := by
  have h0 (q : Pattern) (selected : d14466 q = 2) : d163496 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d14466, d163496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14295 q selected
    | true =>
      simp only [d14466, d163496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14349 q selected
  have h1 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h2 (q : Pattern) (selected : d14755 q = 2) : d163523 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d14755, d163523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d14755, d163523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14407 q selected
  have h3 (q : Pattern) (selected : d14756 q = 2) : d163524 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d14756, d163524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14756, d163524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d15147 q = 2) : d163559 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d15147, d163559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d15147, d163559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14480 q selected
  have h5 (q : Pattern) (selected : d15148 q = 2) : d163560 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d15148, d163560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d15148, d163560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15149 q = 2) : d163561 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d15149, d163561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15149, d163561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d15540 q = 2) : d163596 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d15540, d163596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d15540, d163596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14553 q selected
  have h8 (q : Pattern) (selected : d15541 q = 2) : d163597 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d15541, d163597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d15541, d163597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d15542 q = 2) : d163598 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d15542, d163598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d15542, d163598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d15543 q = 2) : d163599 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d15543, d163599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15543, d163599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d15918 q = 2) : d163634 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d15918, d163634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d15918, d163634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14626 q selected
  have h12 (q : Pattern) (selected : d15919 q = 2) : d163635 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d15919, d163635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d15919, d163635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d15920 q = 2) : d163636 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d15920, d163636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d15920, d163636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d15921 q = 2) : d163637 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d15921, d163637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d15921, d163637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d15922 q = 2) : d163638 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d15922, d163638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d15922, d163638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d15923 q = 2) : d163639 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d15923, d163639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d15923, d163639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro14628 (p : Pattern) (selected : d15929 p = 2) : d163645 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15924 q = 2) : d163640 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d15924, d163640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14627 q selected
    | true =>
      simp only [d15924, d163640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15925 q = 2) : d163641 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d15925, d163641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d15925, d163641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15926 q = 2) : d163642 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d15926, d163642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15926, d163642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15927 q = 2) : d163643 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d15927, d163643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15927, d163643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15928 q = 2) : d163644 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d15928, d163644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d15928, d163644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d15929 q = 2) : d163645 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d15929, d163645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15929, d163645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14629 (p : Pattern) (selected : d15935 p = 2) : d163651 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15930 q = 2) : d163646 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d15930, d163646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14628 q selected
    | true =>
      simp only [d15930, d163646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15931 q = 2) : d163647 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d15931, d163647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d15931, d163647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15932 q = 2) : d163648 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d15932, d163648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15932, d163648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15933 q = 2) : d163649 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d15933, d163649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15933, d163649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15934 q = 2) : d163650 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d15934, d163650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d15934, d163650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d15935 q = 2) : d163651 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d15935, d163651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15935, d163651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14630 (p : Pattern) (selected : d15941 p = 2) : d163657 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15936 q = 2) : d163652 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d15936, d163652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14629 q selected
    | true =>
      simp only [d15936, d163652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15937 q = 2) : d163653 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d15937, d163653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d15937, d163653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15938 q = 2) : d163654 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d15938, d163654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15938, d163654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15939 q = 2) : d163655 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d15939, d163655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15939, d163655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15940 q = 2) : d163656 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d15940, d163656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d15940, d163656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d15941 q = 2) : d163657 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d15941, d163657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15941, d163657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14631 (p : Pattern) (selected : d15947 p = 2) : d163663 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15942 q = 2) : d163658 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d15942, d163658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14630 q selected
    | true =>
      simp only [d15942, d163658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15943 q = 2) : d163659 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d15943, d163659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d15943, d163659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15944 q = 2) : d163660 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d15944, d163660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15944, d163660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15945 q = 2) : d163661 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d15945, d163661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15945, d163661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15946 q = 2) : d163662 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d15946, d163662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d15946, d163662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d15947 q = 2) : d163663 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d15947, d163663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15947, d163663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14632 (p : Pattern) (selected : d15953 p = 2) : d163669 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15948 q = 2) : d163664 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d15948, d163664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14631 q selected
    | true =>
      simp only [d15948, d163664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15949 q = 2) : d163665 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d15949, d163665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d15949, d163665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15950 q = 2) : d163666 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d15950, d163666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15950, d163666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15951 q = 2) : d163667 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d15951, d163667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15951, d163667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15952 q = 2) : d163668 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d15952, d163668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d15952, d163668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d15953 q = 2) : d163669 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d15953, d163669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15953, d163669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14633 (p : Pattern) (selected : d15959 p = 2) : d163675 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15954 q = 2) : d163670 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d15954, d163670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14632 q selected
    | true =>
      simp only [d15954, d163670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15955 q = 2) : d163671 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d15955, d163671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d15955, d163671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15956 q = 2) : d163672 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d15956, d163672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15956, d163672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15957 q = 2) : d163673 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d15957, d163673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15957, d163673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15958 q = 2) : d163674 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d15958, d163674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d15958, d163674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d15959 q = 2) : d163675 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d15959, d163675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15959, d163675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14634 (p : Pattern) (selected : d15965 p = 2) : d163681 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d15960 q = 2) : d163676 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d15960, d163676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14633 q selected
    | true =>
      simp only [d15960, d163676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d15961 q = 2) : d163677 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d15961, d163677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d15961, d163677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15962 q = 2) : d163678 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d15962, d163678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d15962, d163678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15963 q = 2) : d163679 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d15963, d163679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15963, d163679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15964 q = 2) : d163680 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d15964, d163680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d15964, d163680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d15965 q = 2) : d163681 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d15965, d163681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15965, d163681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14635 (p : Pattern) (selected : d163716 p = 0) : d165071 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25 q = 0) : d51877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro187 q selected
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d26 q = 0) : d51878 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d163715 q = 0) : d165070 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d163715, d165070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163715, d165070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163716 q = 0) : d165071 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d163716, d165071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d163716, d165071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro14636 (p : Pattern) (selected : d163722 p = 0) : d165077 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163717 q = 0) : d165072 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d163717, d165072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14635 q selected
    | true =>
      simp only [d163717, d165072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d163718 q = 0) : d165073 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d163718, d165073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163718, d165073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163719 q = 0) : d165074 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d163719, d165074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163719, d165074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d163720 q = 0) : d165075 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d163720, d165075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d163720, d165075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d163721 q = 0) : d165076 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d163721, d165076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d163721, d165076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d163722 q = 0) : d165077 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d163722, d165077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d163722, d165077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14637 (p : Pattern) (selected : d163728 p = 0) : d165083 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163723 q = 0) : d165078 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163723, d165078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14636 q selected
    | true =>
      simp only [d163723, d165078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d163724 q = 0) : d165079 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163724, d165079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163724, d165079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163725 q = 0) : d165080 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d163725, d165080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163725, d165080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163726 q = 0) : d165081 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d163726, d165081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d163726, d165081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d163727 q = 0) : d165082 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d163727, d165082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d163727, d165082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d163728 q = 0) : d165083 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d163728, d165083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163728, d165083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14638 (p : Pattern) (selected : d163734 p = 0) : d165089 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163729 q = 0) : d165084 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163729, d165084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14637 q selected
    | true =>
      simp only [d163729, d165084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d163730 q = 0) : d165085 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163730, d165085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d163730, d165085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d163731 q = 0) : d165086 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163731, d165086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163731, d165086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163732 q = 0) : d165087 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163732, d165087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163732, d165087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d163733 q = 0) : d165088 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163733, d165088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163733, d165088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d163734 q = 0) : d165089 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163734, d165089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163734, d165089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14639 (p : Pattern) (selected : d163735 p = 0) : d165090 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163723 q = 0) : d165078 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163723, d165078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14636 q selected
    | true =>
      simp only [d163723, d165078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d163724 q = 0) : d165079 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163724, d165079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163724, d165079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163725 q = 0) : d165080 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d163725, d165080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163725, d165080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163726 q = 0) : d165081 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d163726, d165081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d163726, d165081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d163727 q = 0) : d165082 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d163727, d165082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d163727, d165082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d163735 q = 0) : d165090 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d163735, d165090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d163735, d165090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14640 (p : Pattern) (selected : d163741 p = 0) : d165096 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163729 q = 0) : d165084 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163729, d165084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14637 q selected
    | true =>
      simp only [d163729, d165084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d163730 q = 0) : d165085 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163730, d165085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d163730, d165085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d163731 q = 0) : d165086 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163731, d165086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163731, d165086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163732 q = 0) : d165087 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163732, d165087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163732, d165087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d163733 q = 0) : d165088 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163733, d165088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163733, d165088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d163736 q = 0) : d165091 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163736, d165091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14639 q selected
    | true =>
      simp only [d163736, d165091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d163737 q = 0) : d165092 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163737, d165092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d163737, d165092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d163738 q = 0) : d165093 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163738, d165093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d163738, d165093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d163739 q = 0) : d165094 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163739, d165094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163739, d165094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d163740 q = 0) : d165095 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163740, d165095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163740, d165095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d163741 q = 0) : d165096 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163741, d165096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d163741, d165096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14641 (p : Pattern) (selected : d163746 p = 0) : d165101 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163736 q = 0) : d165091 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163736, d165091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14639 q selected
    | true =>
      simp only [d163736, d165091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d163737 q = 0) : d165092 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163737, d165092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d163737, d165092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d163738 q = 0) : d165093 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163738, d165093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163738, d165093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163739 q = 0) : d165094 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163739, d165094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163739, d165094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d163740 q = 0) : d165095 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163740, d165095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163740, d165095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d163746 q = 0) : d165101 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163746, d165101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163746, d165101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14642 (p : Pattern) (selected : d163753 p = 0) : d165108 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163742 q = 0) : d165097 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163742, d165097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14638 q selected
    | true =>
      simp only [d163742, d165097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14640 q selected
  have h2 (q : Pattern) (selected : d163743 q = 0) : d165098 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163743, d165098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d163743, d165098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d163744 q = 0) : d165099 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163744, d165099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163744, d165099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163745 q = 0) : d165100 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163745, d165100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163745, d165100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d163747 q = 0) : d165102 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163747, d165102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163747, d165102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14641 q selected
  have h6 (q : Pattern) (selected : d163748 q = 0) : d165103 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163748, d165103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d163748, d165103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d163749 q = 0) : d165104 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163749, d165104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d163749, d165104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d163750 q = 0) : d165105 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163750, d165105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d163750, d165105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d163751 q = 0) : d165106 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163751, d165106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d163751, d165106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d163752 q = 0) : d165107 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163752, d165107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d163752, d165107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d163753 q = 0) : d165108 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d163753, d165108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d163753, d165108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14643 (p : Pattern) (selected : d163762 p = 0) : d165117 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163729 q = 0) : d165084 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163729, d165084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14637 q selected
    | true =>
      simp only [d163729, d165084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d163758 q = 0) : d165113 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163758, d165113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163758, d165113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163759 q = 0) : d165114 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163759, d165114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163759, d165114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163760 q = 0) : d165115 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163760, d165115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163760, d165115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d163761 q = 0) : d165116 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163761, d165116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163761, d165116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d163762 q = 0) : d165117 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163762, d165117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163762, d165117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14644 (p : Pattern) (selected : d163769 p = 0) : d165124 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163729 q = 0) : d165084 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163729, d165084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14637 q selected
    | true =>
      simp only [d163729, d165084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d163758 q = 0) : d165113 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163758, d165113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163758, d165113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163759 q = 0) : d165114 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163759, d165114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163759, d165114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163760 q = 0) : d165115 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163760, d165115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163760, d165115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d163761 q = 0) : d165116 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163761, d165116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163761, d165116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d163736 q = 0) : d165091 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163736, d165091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14639 q selected
    | true =>
      simp only [d163736, d165091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d163765 q = 0) : d165120 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163765, d165120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163765, d165120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d163766 q = 0) : d165121 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163766, d165121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d163766, d165121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d163767 q = 0) : d165122 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163767, d165122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163767, d165122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d163768 q = 0) : d165123 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163768, d165123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163768, d165123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d163769 q = 0) : d165124 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163769, d165124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d163769, d165124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14645 (p : Pattern) (selected : d163774 p = 0) : d165129 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163723 q = 0) : d165078 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163723, d165078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14636 q selected
    | true =>
      simp only [d163723, d165078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d163724 q = 0) : d165079 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163724, d165079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163724, d165079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163725 q = 0) : d165080 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d163725, d165080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163725, d165080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163726 q = 0) : d165081 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d163726, d165081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d163726, d165081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d163773 q = 0) : d165128 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d163773, d165128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163773, d165128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d163774 q = 0) : d165129 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d163774, d165129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163774, d165129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14646 (p : Pattern) (selected : d163781 p = 0) : d165136 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163723 q = 0) : d165078 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163723, d165078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14636 q selected
    | true =>
      simp only [d163723, d165078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d163724 q = 0) : d165079 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163724, d165079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163724, d165079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163725 q = 0) : d165080 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d163725, d165080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163725, d165080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163779 q = 0) : d165134 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d163779, d165134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163779, d165134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d163780 q = 0) : d165135 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d163780, d165135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d163780, d165135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d163781 q = 0) : d165136 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d163781, d165136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163781, d165136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14647 (p : Pattern) (selected : d163786 p = 0) : d165141 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d139 q = 0) : d51990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro205 q selected
    | true =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d140 q = 0) : d51991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d25 q = 0) : d51877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro187 q selected
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d26 q = 0) : d51878 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d163785 q = 0) : d165140 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d163785, d165140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163785, d165140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d163715 q = 0) : d165070 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d163715, d165070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d163715, d165070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d163786 q = 0) : d165141 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d163786, d165141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d163786, d165141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro14648 (p : Pattern) (selected : d163792 p = 0) : d165147 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163787 q = 0) : d165142 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d163787, d165142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14647 q selected
    | true =>
      simp only [d163787, d165142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14635 q selected
  have h2 (q : Pattern) (selected : d163788 q = 0) : d165143 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d163788, d165143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163788, d165143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163789 q = 0) : d165144 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d163789, d165144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163789, d165144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d163717 q = 0) : d165072 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d163717, d165072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14635 q selected
    | true =>
      simp only [d163717, d165072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d163718 q = 0) : d165073 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d163718, d165073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163718, d165073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d163719 q = 0) : d165074 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d163719, d165074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163719, d165074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d163790 q = 0) : d165145 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d163790, d165145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d163790, d165145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d163720 q = 0) : d165075 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d163720, d165075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d163720, d165075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d163791 q = 0) : d165146 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d163791, d165146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d163791, d165146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d163792 q = 0) : d165147 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d163792, d165147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d163792, d165147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro14649 (p : Pattern) (selected : d163798 p = 0) : d165153 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163793 q = 0) : d165148 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163793, d165148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14648 q selected
    | true =>
      simp only [d163793, d165148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d163794 q = 0) : d165149 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163794, d165149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163794, d165149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163723 q = 0) : d165078 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163723, d165078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14636 q selected
    | true =>
      simp only [d163723, d165078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163724 q = 0) : d165079 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163724, d165079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163724, d165079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d163795 q = 0) : d165150 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d163795, d165150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163795, d165150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d163796 q = 0) : d165151 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d163796, d165151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d163796, d165151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d163797 q = 0) : d165152 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d163797, d165152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d163797, d165152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d163798 q = 0) : d165153 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d163798, d165153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163798, d165153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14650 (p : Pattern) (selected : d163801 p = 0) : d165071 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d170 q = 0) : d51877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d170, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro210 q selected
    | true =>
      simp only [d170, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d171 q = 0) : d51878 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d171, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d171, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d163800 q = 0) : d165070 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d163800, d165070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163800, d165070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163801 q = 0) : d165071 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d163801, d165071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d163801, d165071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro14651 (p : Pattern) (selected : d163807 p = 0) : d165077 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163802 q = 0) : d165072 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d163802, d165072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14650 q selected
    | true =>
      simp only [d163802, d165072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d163803 q = 0) : d165073 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d163803, d165073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163803, d165073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163804 q = 0) : d165074 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d163804, d165074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163804, d165074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d163805 q = 0) : d165075 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d163805, d165075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d163805, d165075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d163806 q = 0) : d165076 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d163806, d165076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d163806, d165076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d163807 q = 0) : d165077 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d163807, d165077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d163807, d165077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14652 (p : Pattern) (selected : d163813 p = 0) : d165083 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163808 q = 0) : d165078 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163808, d165078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14651 q selected
    | true =>
      simp only [d163808, d165078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d163809 q = 0) : d165079 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163809, d165079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163809, d165079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163810 q = 0) : d165080 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d163810, d165080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163810, d165080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163811 q = 0) : d165081 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d163811, d165081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d163811, d165081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d163812 q = 0) : d165082 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d163812, d165082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d163812, d165082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d163813 q = 0) : d165083 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d163813, d165083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163813, d165083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14653 (p : Pattern) (selected : d163819 p = 0) : d165159 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163775 q = 0) : d165130 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163775, d165130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14645 q selected
    | true =>
      simp only [d163775, d165130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d163776 q = 0) : d165131 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163776, d165131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163776, d165131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163777 q = 0) : d165132 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163777, d165132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163777, d165132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163778 q = 0) : d165133 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163778, d165133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163778, d165133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d163782 q = 0) : d165137 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163782, d165137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14646 q selected
    | true =>
      simp only [d163782, d165137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d163783 q = 0) : d165138 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163783, d165138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163783, d165138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d163784 q = 0) : d165139 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163784, d165139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d163784, d165139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d163799 q = 0) : d165154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163799, d165154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14649 q selected
    | true =>
      simp only [d163799, d165154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14637 q selected
  have h9 (q : Pattern) (selected : d163814 q = 0) : d165084 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163814, d165084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14652 q selected
    | true =>
      simp only [d163814, d165084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d163815 q = 0) : d165155 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163815, d165155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d163815, d165155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d163729 q = 0) : d165084 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163729, d165084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14637 q selected
    | true =>
      simp only [d163729, d165084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d163730 q = 0) : d165085 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163730, d165085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d163730, d165085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d163816 q = 0) : d165156 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163816, d165156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d163816, d165156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d163817 q = 0) : d165157 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163817, d165157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d163817, d165157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d163818 q = 0) : d165158 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163818, d165158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d163818, d165158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d163819 q = 0) : d165159 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163819, d165159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163819, d165159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro14654 (p : Pattern) (selected : d163820 p = 0) : d165160 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163723 q = 0) : d165078 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163723, d165078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14636 q selected
    | true =>
      simp only [d163723, d165078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d163724 q = 0) : d165079 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163724, d165079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163724, d165079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163725 q = 0) : d165080 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d163725, d165080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163725, d165080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163726 q = 0) : d165081 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d163726, d165081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d163726, d165081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d163773 q = 0) : d165128 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d163773, d165128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163773, d165128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d163820 q = 0) : d165160 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d163820, d165160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d163820, d165160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14655 (p : Pattern) (selected : d163825 p = 0) : d165165 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163723 q = 0) : d165078 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163723, d165078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14636 q selected
    | true =>
      simp only [d163723, d165078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d163724 q = 0) : d165079 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163724, d165079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163724, d165079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163725 q = 0) : d165080 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d163725, d165080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163725, d165080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163779 q = 0) : d165134 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d163779, d165134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163779, d165134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d163780 q = 0) : d165135 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d163780, d165135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d163780, d165135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d163825 q = 0) : d165165 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d163825, d165165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d163825, d165165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14656 (p : Pattern) (selected : d163829 p = 0) : d165169 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163793 q = 0) : d165148 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163793, d165148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14648 q selected
    | true =>
      simp only [d163793, d165148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d163794 q = 0) : d165149 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163794, d165149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163794, d165149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163723 q = 0) : d165078 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163723, d165078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14636 q selected
    | true =>
      simp only [d163723, d165078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163724 q = 0) : d165079 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163724, d165079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163724, d165079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d163795 q = 0) : d165150 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d163795, d165150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163795, d165150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d163796 q = 0) : d165151 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d163796, d165151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d163796, d165151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d163797 q = 0) : d165152 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d163797, d165152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d163797, d165152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d163829 q = 0) : d165169 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d163829, d165169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d163829, d165169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14657 (p : Pattern) (selected : d163831 p = 0) : d165090 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163808 q = 0) : d165078 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163808, d165078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14651 q selected
    | true =>
      simp only [d163808, d165078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d163809 q = 0) : d165079 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163809, d165079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163809, d165079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163810 q = 0) : d165080 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d163810, d165080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163810, d165080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163811 q = 0) : d165081 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d163811, d165081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d163811, d165081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d163812 q = 0) : d165082 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d163812, d165082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d163812, d165082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d163831 q = 0) : d165090 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d163831, d165090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d163831, d165090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14658 (p : Pattern) (selected : d163837 p = 0) : d165175 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163775 q = 0) : d165130 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163775, d165130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14645 q selected
    | true =>
      simp only [d163775, d165130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d163776 q = 0) : d165131 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163776, d165131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163776, d165131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163777 q = 0) : d165132 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163777, d165132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163777, d165132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163778 q = 0) : d165133 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163778, d165133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163778, d165133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d163782 q = 0) : d165137 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163782, d165137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14646 q selected
    | true =>
      simp only [d163782, d165137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d163783 q = 0) : d165138 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163783, d165138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163783, d165138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d163784 q = 0) : d165139 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163784, d165139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d163784, d165139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d163799 q = 0) : d165154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163799, d165154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14649 q selected
    | true =>
      simp only [d163799, d165154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14637 q selected
  have h9 (q : Pattern) (selected : d163814 q = 0) : d165084 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163814, d165084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14652 q selected
    | true =>
      simp only [d163814, d165084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d163815 q = 0) : d165155 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163815, d165155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d163815, d165155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d163729 q = 0) : d165084 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163729, d165084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14637 q selected
    | true =>
      simp only [d163729, d165084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d163730 q = 0) : d165085 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163730, d165085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d163730, d165085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d163816 q = 0) : d165156 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163816, d165156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d163816, d165156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d163817 q = 0) : d165157 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163817, d165157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d163817, d165157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d163818 q = 0) : d165158 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163818, d165158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d163818, d165158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d163821 q = 0) : d165161 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163821, d165161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14654 q selected
    | true =>
      simp only [d163821, d165161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d163822 q = 0) : d165162 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163822, d165162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163822, d165162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d163823 q = 0) : d165163 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163823, d165163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d163823, d165163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d163824 q = 0) : d165164 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163824, d165164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163824, d165164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d163826 q = 0) : d165166 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163826, d165166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14655 q selected
    | true =>
      simp only [d163826, d165166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d163827 q = 0) : d165167 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163827, d165167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163827, d165167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d163828 q = 0) : d165168 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163828, d165168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d163828, d165168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d163830 q = 0) : d165170 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163830, d165170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14656 q selected
    | true =>
      simp only [d163830, d165170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14639 q selected
  have h24 (q : Pattern) (selected : d163832 q = 0) : d165091 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163832, d165091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14657 q selected
    | true =>
      simp only [d163832, d165091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d163833 q = 0) : d165171 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163833, d165171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d163833, d165171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d163736 q = 0) : d165091 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163736, d165091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14639 q selected
    | true =>
      simp only [d163736, d165091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d163737 q = 0) : d165092 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163737, d165092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d163737, d165092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d163834 q = 0) : d165172 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163834, d165172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d163834, d165172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d163835 q = 0) : d165173 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163835, d165173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d163835, d165173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d163836 q = 0) : d165174 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163836, d165174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d163836, d165174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d163837 q = 0) : d165175 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163837, d165175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d163837, d165175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro14659 (p : Pattern) (selected : d163839 p = 0) : d165177 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163729 q = 0) : d165084 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163729, d165084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14637 q selected
    | true =>
      simp only [d163729, d165084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d163758 q = 0) : d165113 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163758, d165113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163758, d165113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163759 q = 0) : d165114 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163759, d165114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163759, d165114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163760 q = 0) : d165115 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163760, d165115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163760, d165115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d163761 q = 0) : d165116 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163761, d165116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163761, d165116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d163839 q = 0) : d165177 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163839, d165177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d163839, d165177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14660 (p : Pattern) (selected : d163846 p = 0) : d165184 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163830 q = 0) : d165170 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163830, d165170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14656 q selected
    | true =>
      simp only [d163830, d165170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14639 q selected
  have h2 (q : Pattern) (selected : d163832 q = 0) : d165091 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163832, d165091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14657 q selected
    | true =>
      simp only [d163832, d165091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d163833 q = 0) : d165171 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163833, d165171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d163833, d165171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d163736 q = 0) : d165091 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163736, d165091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14639 q selected
    | true =>
      simp only [d163736, d165091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d163737 q = 0) : d165092 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163737, d165092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d163737, d165092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d163834 q = 0) : d165172 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163834, d165172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d163834, d165172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d163844 q = 0) : d165182 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163844, d165182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163844, d165182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d163845 q = 0) : d165183 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163845, d165183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163845, d165183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d163846 q = 0) : d165184 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163846, d165184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163846, d165184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro14661 (p : Pattern) (selected : d163853 p = 0) : d165191 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163763 q = 0) : d165118 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163763, d165118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163763, d165118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14643 q selected
  have h2 (q : Pattern) (selected : d163764 q = 0) : d165119 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163764, d165119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d163764, d165119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d163770 q = 0) : d165125 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163770, d165125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14643 q selected
    | true =>
      simp only [d163770, d165125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14644 q selected
  have h4 (q : Pattern) (selected : d163771 q = 0) : d165126 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163771, d165126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d163771, d165126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d163772 q = 0) : d165127 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163772, d165127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163772, d165127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d163838 q = 0) : d165176 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163838, d165176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14653 q selected
    | true =>
      simp only [d163838, d165176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14658 q selected
  have h7 (q : Pattern) (selected : d163840 q = 0) : d165178 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163840, d165178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14659 q selected
    | true =>
      simp only [d163840, d165178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d163841 q = 0) : d165179 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163841, d165179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d163841, d165179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d163842 q = 0) : d165180 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163842, d165180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d163842, d165180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d163843 q = 0) : d165181 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163843, d165181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d163843, d165181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d163847 q = 0) : d165185 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163847, d165185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163847, d165185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14660 q selected
  have h12 (q : Pattern) (selected : d163848 q = 0) : d165186 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163848, d165186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d163848, d165186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d163849 q = 0) : d165187 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163849, d165187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d163849, d165187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d163850 q = 0) : d165188 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163850, d165188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d163850, d165188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d163851 q = 0) : d165189 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163851, d165189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d163851, d165189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d163852 q = 0) : d165190 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163852, d165190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d163852, d165190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d163853 q = 0) : d165191 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d163853, d165191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d163853, d165191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro14662 (p : Pattern) (selected : d163863 p = 0) : d165201 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163799 q = 0) : d165154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163799, d165154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14649 q selected
    | true =>
      simp only [d163799, d165154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14637 q selected
  have h2 (q : Pattern) (selected : d163859 q = 0) : d165197 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163859, d165197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163859, d165197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163860 q = 0) : d165198 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163860, d165198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163860, d165198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163861 q = 0) : d165199 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163861, d165199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163861, d165199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d163862 q = 0) : d165200 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163862, d165200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163862, d165200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d163863 q = 0) : d165201 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163863, d165201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163863, d165201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14663 (p : Pattern) (selected : d163870 p = 0) : d165208 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163799 q = 0) : d165154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163799, d165154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14649 q selected
    | true =>
      simp only [d163799, d165154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14637 q selected
  have h2 (q : Pattern) (selected : d163859 q = 0) : d165197 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163859, d165197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163859, d165197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163860 q = 0) : d165198 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163860, d165198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163860, d165198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163861 q = 0) : d165199 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163861, d165199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163861, d165199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d163862 q = 0) : d165200 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163862, d165200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163862, d165200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d163830 q = 0) : d165170 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163830, d165170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14656 q selected
    | true =>
      simp only [d163830, d165170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14639 q selected
  have h7 (q : Pattern) (selected : d163866 q = 0) : d165204 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163866, d165204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163866, d165204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d163867 q = 0) : d165205 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163867, d165205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d163867, d165205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d163868 q = 0) : d165206 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163868, d165206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163868, d165206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d163869 q = 0) : d165207 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163869, d165207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163869, d165207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d163870 q = 0) : d165208 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163870, d165208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d163870, d165208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14664 (p : Pattern) (selected : d163875 p = 0) : d165213 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163793 q = 0) : d165148 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163793, d165148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14648 q selected
    | true =>
      simp only [d163793, d165148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d163794 q = 0) : d165149 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163794, d165149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163794, d165149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163723 q = 0) : d165078 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163723, d165078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14636 q selected
    | true =>
      simp only [d163723, d165078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163724 q = 0) : d165079 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163724, d165079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163724, d165079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d163795 q = 0) : d165150 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d163795, d165150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163795, d165150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d163796 q = 0) : d165151 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d163796, d165151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d163796, d165151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d163874 q = 0) : d165212 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d163874, d165212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163874, d165212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d163875 q = 0) : d165213 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d163875, d165213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163875, d165213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14665 (p : Pattern) (selected : d163882 p = 0) : d165220 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163793 q = 0) : d165148 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163793, d165148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14648 q selected
    | true =>
      simp only [d163793, d165148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d163794 q = 0) : d165149 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163794, d165149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163794, d165149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163723 q = 0) : d165078 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163723, d165078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14636 q selected
    | true =>
      simp only [d163723, d165078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163724 q = 0) : d165079 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163724, d165079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163724, d165079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d163795 q = 0) : d165150 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d163795, d165150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163795, d165150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d163880 q = 0) : d165218 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d163880, d165218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163880, d165218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d163881 q = 0) : d165219 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d163881, d165219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d163881, d165219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d163882 q = 0) : d165220 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d163882, d165220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163882, d165220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14666 (p : Pattern) (selected : d163888 p = 0) : d165226 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d319 q = 0) : d52118 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro235 q selected
    | true =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d320 q = 0) : d52119 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d139 q = 0) : d51990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro205 q selected
    | true =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d140 q = 0) : d51991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d163886 q = 0) : d165224 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d163886, d165224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163886, d165224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9382 q = 0) : d101015 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6607 q selected
    | true =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d9384 q = 0) : d101017 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d101017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9384, d101017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d25 q = 0) : d51877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro187 q selected
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d26 q = 0) : d51878 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d163887 q = 0) : d165225 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d163887, d165225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d163887, d165225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d163888 q = 0) : d165226 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d163888, d165226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d163888, d165226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14667 (p : Pattern) (selected : d163894 p = 0) : d165232 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163889 q = 0) : d165227 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d163889, d165227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14666 q selected
    | true =>
      simp only [d163889, d165227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14647 q selected
  have h2 (q : Pattern) (selected : d163890 q = 0) : d165228 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d163890, d165228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163890, d165228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163891 q = 0) : d165229 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d163891, d165229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163891, d165229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d163787 q = 0) : d165142 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d163787, d165142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14647 q selected
    | true =>
      simp only [d163787, d165142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14635 q selected
  have h5 (q : Pattern) (selected : d163788 q = 0) : d165143 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d163788, d165143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163788, d165143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d163789 q = 0) : d165144 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d163789, d165144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163789, d165144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d163892 q = 0) : d165230 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d163892, d165230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d163892, d165230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d163717 q = 0) : d165072 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d163717, d165072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14635 q selected
    | true =>
      simp only [d163717, d165072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d163718 q = 0) : d165073 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d163718, d165073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163718, d165073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d163719 q = 0) : d165074 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d163719, d165074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163719, d165074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d163790 q = 0) : d165145 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d163790, d165145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d163790, d165145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d163893 q = 0) : d165231 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d163893, d165231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d163893, d165231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d163894 q = 0) : d165232 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d163894, d165232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d163894, d165232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro14668 (p : Pattern) (selected : d163900 p = 0) : d165238 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163895 q = 0) : d165233 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163895, d165233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14667 q selected
    | true =>
      simp only [d163895, d165233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d163896 q = 0) : d165234 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163896, d165234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163896, d165234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163793 q = 0) : d165148 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163793, d165148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14648 q selected
    | true =>
      simp only [d163793, d165148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163794 q = 0) : d165149 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163794, d165149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163794, d165149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d163897 q = 0) : d165235 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d163897, d165235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163897, d165235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d163898 q = 0) : d165236 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d163898, d165236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d163898, d165236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d163899 q = 0) : d165237 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d163899, d165237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d163899, d165237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d163900 q = 0) : d165238 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d163900, d165238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163900, d165238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14669 (p : Pattern) (selected : d163903 p = 0) : d165141 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d350 q = 0) : d51990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d350, d51990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro240 q selected
    | true =>
      simp only [d350, d51990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d351 q = 0) : d51991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d351, d51991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d351, d51991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d170 q = 0) : d51877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d170, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro210 q selected
    | true =>
      simp only [d170, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d171 q = 0) : d51878 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d171, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d171, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d163902 q = 0) : d165140 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d163902, d165140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163902, d165140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d163800 q = 0) : d165070 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d163800, d165070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d163800, d165070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d163903 q = 0) : d165141 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d163903, d165141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d163903, d165141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro14670 (p : Pattern) (selected : d163909 p = 0) : d165147 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163904 q = 0) : d165142 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d163904, d165142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14669 q selected
    | true =>
      simp only [d163904, d165142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14650 q selected
  have h2 (q : Pattern) (selected : d163905 q = 0) : d165143 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d163905, d165143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163905, d165143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163906 q = 0) : d165144 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d163906, d165144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163906, d165144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d163802 q = 0) : d165072 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d163802, d165072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14650 q selected
    | true =>
      simp only [d163802, d165072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d163803 q = 0) : d165073 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d163803, d165073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163803, d165073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d163804 q = 0) : d165074 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d163804, d165074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163804, d165074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d163907 q = 0) : d165145 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d163907, d165145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d163907, d165145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d163805 q = 0) : d165075 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d163805, d165075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d163805, d165075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d163908 q = 0) : d165146 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d163908, d165146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d163908, d165146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d163909 q = 0) : d165147 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d163909, d165147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d163909, d165147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro14671 (p : Pattern) (selected : d163915 p = 0) : d165153 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163910 q = 0) : d165148 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163910, d165148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14670 q selected
    | true =>
      simp only [d163910, d165148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d163911 q = 0) : d165149 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163911, d165149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163911, d165149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163808 q = 0) : d165078 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163808, d165078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14651 q selected
    | true =>
      simp only [d163808, d165078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163809 q = 0) : d165079 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163809, d165079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163809, d165079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d163912 q = 0) : d165150 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d163912, d165150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163912, d165150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d163913 q = 0) : d165151 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d163913, d165151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d163913, d165151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d163914 q = 0) : d165152 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d163914, d165152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d163914, d165152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d163915 q = 0) : d165153 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d163915, d165153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163915, d165153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14672 (p : Pattern) (selected : d163921 p = 0) : d165244 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163793 q = 0) : d165148 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163793, d165148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14648 q selected
    | true =>
      simp only [d163793, d165148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d163794 q = 0) : d165149 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163794, d165149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163794, d165149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163918 q = 0) : d165241 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d163918, d165241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163918, d165241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163919 q = 0) : d165242 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d163919, d165242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d163919, d165242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d163920 q = 0) : d165243 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d163920, d165243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d163920, d165243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d163921 q = 0) : d165244 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d163921, d165244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163921, d165244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14673 (p : Pattern) (selected : d163927 p = 0) : d165250 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163876 q = 0) : d165214 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163876, d165214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14664 q selected
    | true =>
      simp only [d163876, d165214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14645 q selected
  have h2 (q : Pattern) (selected : d163877 q = 0) : d165215 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163877, d165215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163877, d165215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163878 q = 0) : d165216 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163878, d165216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163878, d165216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163879 q = 0) : d165217 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163879, d165217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163879, d165217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d163883 q = 0) : d165221 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163883, d165221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14665 q selected
    | true =>
      simp only [d163883, d165221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14646 q selected
  have h6 (q : Pattern) (selected : d163884 q = 0) : d165222 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163884, d165222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163884, d165222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d163885 q = 0) : d165223 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163885, d165223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d163885, d165223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d163901 q = 0) : d165239 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163901, d165239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14668 q selected
    | true =>
      simp only [d163901, d165239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14649 q selected
  have h9 (q : Pattern) (selected : d163916 q = 0) : d165154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163916, d165154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14671 q selected
    | true =>
      simp only [d163916, d165154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14652 q selected
  have h10 (q : Pattern) (selected : d163917 q = 0) : d165240 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163917, d165240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d163917, d165240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d163922 q = 0) : d165245 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163922, d165245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14672 q selected
    | true =>
      simp only [d163922, d165245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d163923 q = 0) : d165246 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163923, d165246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d163923, d165246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d163924 q = 0) : d165247 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163924, d165247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d163924, d165247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d163925 q = 0) : d165248 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163925, d165248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d163925, d165248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d163926 q = 0) : d165249 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163926, d165249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d163926, d165249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d163927 q = 0) : d165250 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163927, d165250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163927, d165250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro14674 (p : Pattern) (selected : d163928 p = 0) : d165251 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163793 q = 0) : d165148 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163793, d165148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14648 q selected
    | true =>
      simp only [d163793, d165148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d163794 q = 0) : d165149 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163794, d165149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163794, d165149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163723 q = 0) : d165078 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163723, d165078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14636 q selected
    | true =>
      simp only [d163723, d165078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163724 q = 0) : d165079 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163724, d165079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163724, d165079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d163795 q = 0) : d165150 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d163795, d165150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163795, d165150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d163796 q = 0) : d165151 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d163796, d165151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d163796, d165151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d163874 q = 0) : d165212 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d163874, d165212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163874, d165212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d163928 q = 0) : d165251 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d163928, d165251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d163928, d165251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14675 (p : Pattern) (selected : d163933 p = 0) : d165256 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163793 q = 0) : d165148 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163793, d165148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14648 q selected
    | true =>
      simp only [d163793, d165148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d163794 q = 0) : d165149 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163794, d165149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163794, d165149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163723 q = 0) : d165078 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163723, d165078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14636 q selected
    | true =>
      simp only [d163723, d165078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163724 q = 0) : d165079 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163724, d165079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163724, d165079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d163795 q = 0) : d165150 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d163795, d165150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163795, d165150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d163880 q = 0) : d165218 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d163880, d165218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163880, d165218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d163881 q = 0) : d165219 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d163881, d165219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d163881, d165219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d163933 q = 0) : d165256 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d163933, d165256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d163933, d165256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14676 (p : Pattern) (selected : d163937 p = 0) : d165260 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163895 q = 0) : d165233 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163895, d165233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14667 q selected
    | true =>
      simp only [d163895, d165233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d163896 q = 0) : d165234 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163896, d165234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163896, d165234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163793 q = 0) : d165148 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163793, d165148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14648 q selected
    | true =>
      simp only [d163793, d165148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163794 q = 0) : d165149 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163794, d165149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163794, d165149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d163897 q = 0) : d165235 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d163897, d165235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163897, d165235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d163898 q = 0) : d165236 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d163898, d165236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d163898, d165236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d163899 q = 0) : d165237 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d163899, d165237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d163899, d165237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d163937 q = 0) : d165260 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d163937, d165260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d163937, d165260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14677 (p : Pattern) (selected : d163939 p = 0) : d165169 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163910 q = 0) : d165148 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163910, d165148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14670 q selected
    | true =>
      simp only [d163910, d165148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d163911 q = 0) : d165149 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163911, d165149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163911, d165149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163808 q = 0) : d165078 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163808, d165078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14651 q selected
    | true =>
      simp only [d163808, d165078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163809 q = 0) : d165079 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163809, d165079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163809, d165079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d163912 q = 0) : d165150 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d163912, d165150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163912, d165150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d163913 q = 0) : d165151 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d163913, d165151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d163913, d165151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d163914 q = 0) : d165152 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d163914, d165152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d163914, d165152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d163939 q = 0) : d165169 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d163939, d165169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d163939, d165169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14678 (p : Pattern) (selected : d163942 p = 0) : d165263 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163793 q = 0) : d165148 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163793, d165148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14648 q selected
    | true =>
      simp only [d163793, d165148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d163794 q = 0) : d165149 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163794, d165149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163794, d165149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163918 q = 0) : d165241 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d163918, d165241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163918, d165241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163919 q = 0) : d165242 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d163919, d165242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d163919, d165242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d163920 q = 0) : d165243 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d163920, d165243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d163920, d165243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d163942 q = 0) : d165263 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d163942, d165263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d163942, d165263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14679 (p : Pattern) (selected : d163948 p = 0) : d165269 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163876 q = 0) : d165214 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163876, d165214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14664 q selected
    | true =>
      simp only [d163876, d165214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14645 q selected
  have h2 (q : Pattern) (selected : d163877 q = 0) : d165215 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163877, d165215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163877, d165215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163878 q = 0) : d165216 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163878, d165216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163878, d165216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163879 q = 0) : d165217 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163879, d165217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163879, d165217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d163883 q = 0) : d165221 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163883, d165221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14665 q selected
    | true =>
      simp only [d163883, d165221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14646 q selected
  have h6 (q : Pattern) (selected : d163884 q = 0) : d165222 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163884, d165222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163884, d165222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d163885 q = 0) : d165223 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163885, d165223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d163885, d165223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d163901 q = 0) : d165239 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163901, d165239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14668 q selected
    | true =>
      simp only [d163901, d165239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14649 q selected
  have h9 (q : Pattern) (selected : d163916 q = 0) : d165154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163916, d165154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14671 q selected
    | true =>
      simp only [d163916, d165154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14652 q selected
  have h10 (q : Pattern) (selected : d163917 q = 0) : d165240 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163917, d165240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d163917, d165240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d163922 q = 0) : d165245 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163922, d165245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14672 q selected
    | true =>
      simp only [d163922, d165245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d163923 q = 0) : d165246 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163923, d165246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d163923, d165246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d163924 q = 0) : d165247 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163924, d165247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d163924, d165247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d163925 q = 0) : d165248 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163925, d165248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d163925, d165248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d163926 q = 0) : d165249 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163926, d165249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d163926, d165249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d163929 q = 0) : d165252 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163929, d165252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14674 q selected
    | true =>
      simp only [d163929, d165252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14654 q selected
  have h17 (q : Pattern) (selected : d163930 q = 0) : d165253 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163930, d165253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163930, d165253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d163931 q = 0) : d165254 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163931, d165254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d163931, d165254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d163932 q = 0) : d165255 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163932, d165255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163932, d165255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d163934 q = 0) : d165257 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163934, d165257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14675 q selected
    | true =>
      simp only [d163934, d165257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14655 q selected
  have h21 (q : Pattern) (selected : d163935 q = 0) : d165258 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163935, d165258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163935, d165258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d163936 q = 0) : d165259 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163936, d165259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d163936, d165259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d163938 q = 0) : d165261 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163938, d165261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14676 q selected
    | true =>
      simp only [d163938, d165261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14656 q selected
  have h24 (q : Pattern) (selected : d163940 q = 0) : d165170 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163940, d165170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14677 q selected
    | true =>
      simp only [d163940, d165170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14657 q selected
  have h25 (q : Pattern) (selected : d163941 q = 0) : d165262 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163941, d165262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d163941, d165262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d163943 q = 0) : d165264 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163943, d165264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14678 q selected
    | true =>
      simp only [d163943, d165264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d163944 q = 0) : d165265 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163944, d165265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d163944, d165265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d163945 q = 0) : d165266 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163945, d165266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d163945, d165266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d163946 q = 0) : d165267 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163946, d165267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d163946, d165267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d163947 q = 0) : d165268 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163947, d165268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d163947, d165268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d163948 q = 0) : d165269 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163948, d165269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d163948, d165269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro14680 (p : Pattern) (selected : d163950 p = 0) : d165271 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163799 q = 0) : d165154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163799, d165154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14649 q selected
    | true =>
      simp only [d163799, d165154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14637 q selected
  have h2 (q : Pattern) (selected : d163859 q = 0) : d165197 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163859, d165197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163859, d165197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163860 q = 0) : d165198 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163860, d165198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163860, d165198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163861 q = 0) : d165199 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163861, d165199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163861, d165199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d163862 q = 0) : d165200 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163862, d165200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163862, d165200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d163729 q = 0) : d165084 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163729, d165084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14637 q selected
    | true =>
      simp only [d163729, d165084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d163758 q = 0) : d165113 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163758, d165113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163758, d165113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d163759 q = 0) : d165114 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163759, d165114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d163759, d165114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d163760 q = 0) : d165115 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163760, d165115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163760, d165115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d163761 q = 0) : d165116 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163761, d165116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163761, d165116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d163950 q = 0) : d165271 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163950, d165271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d163950, d165271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14681 (p : Pattern) (selected : d163957 p = 0) : d165278 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163938 q = 0) : d165261 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163938, d165261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14676 q selected
    | true =>
      simp only [d163938, d165261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14656 q selected
  have h2 (q : Pattern) (selected : d163940 q = 0) : d165170 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163940, d165170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14677 q selected
    | true =>
      simp only [d163940, d165170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14657 q selected
  have h3 (q : Pattern) (selected : d163941 q = 0) : d165262 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163941, d165262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d163941, d165262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d163943 q = 0) : d165264 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163943, d165264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14678 q selected
    | true =>
      simp only [d163943, d165264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d163944 q = 0) : d165265 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163944, d165265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d163944, d165265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d163945 q = 0) : d165266 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163945, d165266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d163945, d165266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d163955 q = 0) : d165276 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163955, d165276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163955, d165276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d163956 q = 0) : d165277 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163956, d165277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163956, d165277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d163957 q = 0) : d165278 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163957, d165278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163957, d165278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro14682 (p : Pattern) (selected : d163959 p = 0) : d165280 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163736 q = 0) : d165091 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163736, d165091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14639 q selected
    | true =>
      simp only [d163736, d165091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d163765 q = 0) : d165120 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163765, d165120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163765, d165120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163766 q = 0) : d165121 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163766, d165121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163766, d165121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163767 q = 0) : d165122 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163767, d165122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163767, d165122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d163768 q = 0) : d165123 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163768, d165123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163768, d165123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d163959 q = 0) : d165280 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163959, d165280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163959, d165280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14683 (p : Pattern) (selected : d163966 p = 0) : d165287 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163864 q = 0) : d165202 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163864, d165202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163864, d165202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14662 q selected
  have h2 (q : Pattern) (selected : d163865 q = 0) : d165203 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163865, d165203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d163865, d165203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d163871 q = 0) : d165209 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163871, d165209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14662 q selected
    | true =>
      simp only [d163871, d165209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14663 q selected
  have h4 (q : Pattern) (selected : d163872 q = 0) : d165210 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163872, d165210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d163872, d165210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d163873 q = 0) : d165211 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163873, d165211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163873, d165211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d163949 q = 0) : d165270 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163949, d165270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14673 q selected
    | true =>
      simp only [d163949, d165270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14679 q selected
  have h7 (q : Pattern) (selected : d163951 q = 0) : d165272 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163951, d165272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14680 q selected
    | true =>
      simp only [d163951, d165272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14644 q selected
  have h8 (q : Pattern) (selected : d163952 q = 0) : d165273 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163952, d165273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d163952, d165273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d163953 q = 0) : d165274 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163953, d165274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d163953, d165274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d163954 q = 0) : d165275 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163954, d165275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d163954, d165275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d163958 q = 0) : d165279 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163958, d165279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163958, d165279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14681 q selected
  have h12 (q : Pattern) (selected : d163960 q = 0) : d165281 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163960, d165281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163960, d165281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14682 q selected
  have h13 (q : Pattern) (selected : d163961 q = 0) : d165282 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163961, d165282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d163961, d165282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d163962 q = 0) : d165283 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163962, d165283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d163962, d165283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d163963 q = 0) : d165284 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163963, d165284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d163963, d165284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d163964 q = 0) : d165285 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163964, d165285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d163964, d165285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d163965 q = 0) : d165286 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163965, d165286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d163965, d165286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d163966 q = 0) : d165287 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d163966, d165287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d163966, d165287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro14684 (p : Pattern) (selected : d163972 p = 0) : d165293 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163754 q = 0) : d165109 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d163754, d165109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163754, d165109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14642 q selected
  have h2 (q : Pattern) (selected : d163755 q = 0) : d165110 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d163755, d165110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163755, d165110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163756 q = 0) : d165111 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d163756, d165111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163756, d165111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d163757 q = 0) : d165112 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d163757, d165112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163757, d165112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d163854 q = 0) : d165192 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d163854, d165192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163854, d165192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14661 q selected
  have h6 (q : Pattern) (selected : d163855 q = 0) : d165193 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d163855, d165193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163855, d165193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d163856 q = 0) : d165194 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d163856, d165194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163856, d165194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d163857 q = 0) : d165195 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d163857, d165195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163857, d165195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d163858 q = 0) : d165196 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d163858, d165196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d163858, d165196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d163967 q = 0) : d165288 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d163967, d165288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163967, d165288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14683 q selected
  have h11 (q : Pattern) (selected : d163968 q = 0) : d165289 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d163968, d165289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163968, d165289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d163969 q = 0) : d165290 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d163969, d165290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163969, d165290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d163970 q = 0) : d165291 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d163970, d165291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163970, d165291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d163971 q = 0) : d165292 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d163971, d165292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163971, d165292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d163972 q = 0) : d165293 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d163972, d165293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d163972, d165293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro14685 (p : Pattern) (selected : d163975 p = 0) : d165296 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163889 q = 0) : d165227 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d163889, d165227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14666 q selected
    | true =>
      simp only [d163889, d165227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14647 q selected
  have h2 (q : Pattern) (selected : d163890 q = 0) : d165228 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d163890, d165228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163890, d165228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163891 q = 0) : d165229 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d163891, d165229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163891, d165229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d163787 q = 0) : d165142 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d163787, d165142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14647 q selected
    | true =>
      simp only [d163787, d165142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14635 q selected
  have h5 (q : Pattern) (selected : d163788 q = 0) : d165143 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d163788, d165143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163788, d165143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d163789 q = 0) : d165144 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d163789, d165144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163789, d165144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d163892 q = 0) : d165230 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d163892, d165230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d163892, d165230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d163973 q = 0) : d165294 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d163973, d165294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d163973, d165294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d163974 q = 0) : d165295 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d163974, d165295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d163974, d165295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d163975 q = 0) : d165296 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d163975, d165296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d163975, d165296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro14686 (p : Pattern) (selected : d163979 p = 0) : d165300 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163787 q = 0) : d165142 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d163787, d165142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14647 q selected
    | true =>
      simp only [d163787, d165142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14635 q selected
  have h2 (q : Pattern) (selected : d163788 q = 0) : d165143 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d163788, d165143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163788, d165143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163789 q = 0) : d165144 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d163789, d165144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163789, d165144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d163973 q = 0) : d165294 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d163973, d165294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d163973, d165294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d163978 q = 0) : d165299 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d163978, d165299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d163978, d165299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d163979 q = 0) : d165300 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d163979, d165300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d163979, d165300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14687 (p : Pattern) (selected : d163985 p = 0) : d165306 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163976 q = 0) : d165297 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163976, d165297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14685 q selected
    | true =>
      simp only [d163976, d165297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d163977 q = 0) : d165298 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163977, d165298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163977, d165298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163980 q = 0) : d165301 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163980, d165301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14686 q selected
    | true =>
      simp only [d163980, d165301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163981 q = 0) : d165302 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163981, d165302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163981, d165302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d163982 q = 0) : d165303 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d163982, d165303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163982, d165303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d163983 q = 0) : d165304 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d163983, d165304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d163983, d165304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d163984 q = 0) : d165305 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d163984, d165305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d163984, d165305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d163985 q = 0) : d165306 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d163985, d165306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163985, d165306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14688 (p : Pattern) (selected : d163989 p = 0) : d165310 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163980 q = 0) : d165301 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163980, d165301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14686 q selected
    | true =>
      simp only [d163980, d165301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d163981 q = 0) : d165302 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163981, d165302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163981, d165302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163986 q = 0) : d165307 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d163986, d165307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163986, d165307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163987 q = 0) : d165308 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d163987, d165308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d163987, d165308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d163988 q = 0) : d165309 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d163988, d165309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d163988, d165309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d163989 q = 0) : d165310 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d163989, d165310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163989, d165310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14689 (p : Pattern) (selected : d163995 p = 0) : d165316 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163990 q = 0) : d165311 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163990, d165311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14687 q selected
    | true =>
      simp only [d163990, d165311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14688 q selected
  have h2 (q : Pattern) (selected : d163991 q = 0) : d165312 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163991, d165312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163991, d165312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163992 q = 0) : d165313 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163992, d165313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163992, d165313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163993 q = 0) : d165314 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163993, d165314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163993, d165314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d163994 q = 0) : d165315 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163994, d165315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163994, d165315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d163995 q = 0) : d165316 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163995, d165316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163995, d165316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14690 (p : Pattern) (selected : d163998 p = 0) : d165319 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163976 q = 0) : d165297 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163976, d165297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14685 q selected
    | true =>
      simp only [d163976, d165297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d163977 q = 0) : d165298 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163977, d165298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163977, d165298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163980 q = 0) : d165301 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163980, d165301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14686 q selected
    | true =>
      simp only [d163980, d165301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163981 q = 0) : d165302 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163981, d165302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163981, d165302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d163982 q = 0) : d165303 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d163982, d165303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163982, d165303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d163983 q = 0) : d165304 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d163983, d165304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d163983, d165304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d163984 q = 0) : d165305 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d163984, d165305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d163984, d165305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d163998 q = 0) : d165319 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d163998, d165319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d163998, d165319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14691 (p : Pattern) (selected : d163999 p = 0) : d165320 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163980 q = 0) : d165301 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163980, d165301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14686 q selected
    | true =>
      simp only [d163980, d165301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d163981 q = 0) : d165302 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163981, d165302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163981, d165302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163986 q = 0) : d165307 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d163986, d165307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163986, d165307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163987 q = 0) : d165308 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d163987, d165308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d163987, d165308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d163988 q = 0) : d165309 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d163988, d165309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d163988, d165309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d163999 q = 0) : d165320 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d163999, d165320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d163999, d165320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14692 (p : Pattern) (selected : d164005 p = 0) : d165326 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163990 q = 0) : d165311 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163990, d165311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14687 q selected
    | true =>
      simp only [d163990, d165311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14688 q selected
  have h2 (q : Pattern) (selected : d163991 q = 0) : d165312 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163991, d165312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163991, d165312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163992 q = 0) : d165313 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163992, d165313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163992, d165313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163993 q = 0) : d165314 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163993, d165314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163993, d165314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d163994 q = 0) : d165315 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163994, d165315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163994, d165315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164000 q = 0) : d165321 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164000, d165321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14690 q selected
    | true =>
      simp only [d164000, d165321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14691 q selected
  have h7 (q : Pattern) (selected : d164001 q = 0) : d165322 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164001, d165322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164001, d165322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164002 q = 0) : d165323 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164002, d165323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164002, d165323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d164003 q = 0) : d165324 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164003, d165324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164003, d165324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d164004 q = 0) : d165325 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164004, d165325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164004, d165325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164005 q = 0) : d165326 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d164005, d165326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164005, d165326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14693 (p : Pattern) (selected : d164010 p = 0) : d165331 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163976 q = 0) : d165297 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163976, d165297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14685 q selected
    | true =>
      simp only [d163976, d165297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d163977 q = 0) : d165298 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163977, d165298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163977, d165298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163980 q = 0) : d165301 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163980, d165301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14686 q selected
    | true =>
      simp only [d163980, d165301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163981 q = 0) : d165302 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163981, d165302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163981, d165302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d163982 q = 0) : d165303 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d163982, d165303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163982, d165303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d163983 q = 0) : d165304 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d163983, d165304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d163983, d165304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164009 q = 0) : d165330 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164009, d165330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164009, d165330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164010 q = 0) : d165331 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164010, d165331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164010, d165331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14694 (p : Pattern) (selected : d164012 p = 0) : d165333 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163980 q = 0) : d165301 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163980, d165301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14686 q selected
    | true =>
      simp only [d163980, d165301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d163981 q = 0) : d165302 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163981, d165302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163981, d165302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163986 q = 0) : d165307 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d163986, d165307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163986, d165307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163987 q = 0) : d165308 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d163987, d165308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d163987, d165308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164011 q = 0) : d165332 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164011, d165332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164011, d165332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164012 q = 0) : d165333 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164012, d165333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164012, d165333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14695 (p : Pattern) (selected : d164019 p = 0) : d165340 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163976 q = 0) : d165297 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163976, d165297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14685 q selected
    | true =>
      simp only [d163976, d165297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d163977 q = 0) : d165298 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163977, d165298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163977, d165298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163980 q = 0) : d165301 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163980, d165301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14686 q selected
    | true =>
      simp only [d163980, d165301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163981 q = 0) : d165302 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163981, d165302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163981, d165302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d163982 q = 0) : d165303 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d163982, d165303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163982, d165303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164017 q = 0) : d165338 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164017, d165338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164017, d165338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164018 q = 0) : d165339 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164018, d165339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164018, d165339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164019 q = 0) : d165340 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164019, d165340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164019, d165340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14696 (p : Pattern) (selected : d164022 p = 0) : d165343 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163980 q = 0) : d165301 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163980, d165301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14686 q selected
    | true =>
      simp only [d163980, d165301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d163981 q = 0) : d165302 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163981, d165302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163981, d165302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163986 q = 0) : d165307 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d163986, d165307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163986, d165307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164020 q = 0) : d165341 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164020, d165341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164020, d165341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164021 q = 0) : d165342 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164021, d165342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164021, d165342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164022 q = 0) : d165343 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164022, d165343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164022, d165343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14697 (p : Pattern) (selected : d164028 p = 0) : d165349 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d543 q = 0) : d52290 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro277 q selected
    | true =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d544 q = 0) : d52291 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d9458 q = 0) : d101073 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9458, d101073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6619 q selected
    | true =>
      simp only [d9458, d101073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d9460 q = 0) : d101075 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9460, d101075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d9460, d101075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164026 q = 0) : d165347 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164026, d165347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164026, d165347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9468 q = 0) : d101083 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6620 q selected
    | true =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d9470 q = 0) : d101085 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d9382 q = 0) : d101015 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6607 q selected
    | true =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d9384 q = 0) : d101017 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d101017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d9384, d101017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d164027 q = 0) : d165348 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164027, d165348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164027, d165348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164028 q = 0) : d165349 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164028, d165349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164028, d165349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14698 (p : Pattern) (selected : d164032 p = 0) : d165353 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d9382 q = 0) : d101015 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6607 q selected
    | true =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9384 q = 0) : d101017 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d101017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9384, d101017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d25 q = 0) : d51877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro187 q selected
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d26 q = 0) : d51878 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d163887 q = 0) : d165225 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d163887, d165225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163887, d165225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d163715 q = 0) : d165070 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d163715, d165070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d163715, d165070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164032 q = 0) : d165353 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164032, d165353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164032, d165353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro14699 (p : Pattern) (selected : d164038 p = 0) : d165359 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164029 q = 0) : d165350 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164029, d165350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14697 q selected
    | true =>
      simp only [d164029, d165350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14666 q selected
  have h2 (q : Pattern) (selected : d164030 q = 0) : d165351 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164030, d165351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164030, d165351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164031 q = 0) : d165352 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164031, d165352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164031, d165352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164033 q = 0) : d165354 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164033, d165354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14666 q selected
    | true =>
      simp only [d164033, d165354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14698 q selected
  have h5 (q : Pattern) (selected : d164034 q = 0) : d165355 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164034, d165355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164034, d165355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164035 q = 0) : d165356 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164035, d165356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164035, d165356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164036 q = 0) : d165357 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164036, d165357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164036, d165357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d163889 q = 0) : d165227 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d163889, d165227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14666 q selected
    | true =>
      simp only [d163889, d165227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14647 q selected
  have h9 (q : Pattern) (selected : d163890 q = 0) : d165228 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d163890, d165228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163890, d165228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d163891 q = 0) : d165229 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d163891, d165229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163891, d165229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d163787 q = 0) : d165142 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d163787, d165142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14647 q selected
    | true =>
      simp only [d163787, d165142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14635 q selected
  have h12 (q : Pattern) (selected : d163788 q = 0) : d165143 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d163788, d165143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163788, d165143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d163789 q = 0) : d165144 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d163789, d165144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163789, d165144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d163892 q = 0) : d165230 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d163892, d165230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d163892, d165230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d164037 q = 0) : d165358 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d164037, d165358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164037, d165358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d164038 q = 0) : d165359 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d164038, d165359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d164038, d165359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro14700 (p : Pattern) (selected : d164044 p = 0) : d165365 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164039 q = 0) : d165360 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164039, d165360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14699 q selected
    | true =>
      simp only [d164039, d165360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164040 q = 0) : d165361 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164040, d165361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164040, d165361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163976 q = 0) : d165297 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163976, d165297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14685 q selected
    | true =>
      simp only [d163976, d165297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163977 q = 0) : d165298 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163977, d165298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163977, d165298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164041 q = 0) : d165362 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164041, d165362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164041, d165362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164042 q = 0) : d165363 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164042, d165363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164042, d165363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164043 q = 0) : d165364 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164043, d165364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164043, d165364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164044 q = 0) : d165365 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164044, d165365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164044, d165365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14701 (p : Pattern) (selected : d164048 p = 0) : d165226 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d574 q = 0) : d52118 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d574, d52118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro282 q selected
    | true =>
      simp only [d574, d52118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d575 q = 0) : d52119 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d575, d52119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d575, d52119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d350 q = 0) : d51990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d350, d51990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro240 q selected
    | true =>
      simp only [d350, d51990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d351 q = 0) : d51991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d351, d51991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d351, d51991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164046 q = 0) : d165224 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164046, d165224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164046, d165224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9512 q = 0) : d101015 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9512, d101015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6628 q selected
    | true =>
      simp only [d9512, d101015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d9514 q = 0) : d101017 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9514, d101017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9514, d101017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d170 q = 0) : d51877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d170, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro210 q selected
    | true =>
      simp only [d170, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d171 q = 0) : d51878 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d171, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d171, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d164047 q = 0) : d165225 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164047, d165225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164047, d165225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164048 q = 0) : d165226 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164048, d165226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164048, d165226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14702 (p : Pattern) (selected : d164055 p = 0) : d165296 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164049 q = 0) : d165227 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164049, d165227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14701 q selected
    | true =>
      simp only [d164049, d165227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14669 q selected
  have h2 (q : Pattern) (selected : d164050 q = 0) : d165228 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164050, d165228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164050, d165228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164051 q = 0) : d165229 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164051, d165229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164051, d165229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d163904 q = 0) : d165142 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d163904, d165142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14669 q selected
    | true =>
      simp only [d163904, d165142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14650 q selected
  have h5 (q : Pattern) (selected : d163905 q = 0) : d165143 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d163905, d165143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163905, d165143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d163906 q = 0) : d165144 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d163906, d165144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163906, d165144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164052 q = 0) : d165230 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164052, d165230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164052, d165230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164053 q = 0) : d165294 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164053, d165294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164053, d165294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d164054 q = 0) : d165295 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d164054, d165295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164054, d165295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d164055 q = 0) : d165296 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d164055, d165296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d164055, d165296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro14703 (p : Pattern) (selected : d164059 p = 0) : d165300 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163904 q = 0) : d165142 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d163904, d165142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14669 q selected
    | true =>
      simp only [d163904, d165142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14650 q selected
  have h2 (q : Pattern) (selected : d163905 q = 0) : d165143 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d163905, d165143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163905, d165143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163906 q = 0) : d165144 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d163906, d165144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163906, d165144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164053 q = 0) : d165294 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164053, d165294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164053, d165294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164058 q = 0) : d165299 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d164058, d165299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164058, d165299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164059 q = 0) : d165300 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d164059, d165300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164059, d165300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14704 (p : Pattern) (selected : d164065 p = 0) : d165306 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164056 q = 0) : d165297 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164056, d165297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14702 q selected
    | true =>
      simp only [d164056, d165297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164057 q = 0) : d165298 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164057, d165298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164057, d165298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164060 q = 0) : d165301 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164060, d165301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14703 q selected
    | true =>
      simp only [d164060, d165301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164061 q = 0) : d165302 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164061, d165302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164061, d165302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164062 q = 0) : d165303 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164062, d165303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164062, d165303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164063 q = 0) : d165304 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164063, d165304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164063, d165304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164064 q = 0) : d165305 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164064, d165305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164064, d165305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164065 q = 0) : d165306 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164065, d165306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164065, d165306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14705 (p : Pattern) (selected : d164069 p = 0) : d165310 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164060 q = 0) : d165301 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164060, d165301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14703 q selected
    | true =>
      simp only [d164060, d165301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164061 q = 0) : d165302 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164061, d165302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164061, d165302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164066 q = 0) : d165307 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164066, d165307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164066, d165307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164067 q = 0) : d165308 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164067, d165308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164067, d165308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164068 q = 0) : d165309 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164068, d165309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164068, d165309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164069 q = 0) : d165310 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164069, d165310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164069, d165310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14706 (p : Pattern) (selected : d164075 p = 0) : d165371 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163976 q = 0) : d165297 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163976, d165297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14685 q selected
    | true =>
      simp only [d163976, d165297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d163977 q = 0) : d165298 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163977, d165298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163977, d165298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164072 q = 0) : d165368 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164072, d165368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164072, d165368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164073 q = 0) : d165369 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164073, d165369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164073, d165369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164074 q = 0) : d165370 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164074, d165370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164074, d165370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164075 q = 0) : d165371 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164075, d165371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164075, d165371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14707 (p : Pattern) (selected : d164081 p = 0) : d165377 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164013 q = 0) : d165334 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164013, d165334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14693 q selected
    | true =>
      simp only [d164013, d165334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14694 q selected
  have h2 (q : Pattern) (selected : d164014 q = 0) : d165335 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164014, d165335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164014, d165335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164015 q = 0) : d165336 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164015, d165336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164015, d165336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164016 q = 0) : d165337 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164016, d165337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164016, d165337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164023 q = 0) : d165344 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164023, d165344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14695 q selected
    | true =>
      simp only [d164023, d165344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14696 q selected
  have h6 (q : Pattern) (selected : d164024 q = 0) : d165345 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164024, d165345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164024, d165345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164025 q = 0) : d165346 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164025, d165346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164025, d165346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164045 q = 0) : d165366 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164045, d165366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14700 q selected
    | true =>
      simp only [d164045, d165366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14687 q selected
  have h9 (q : Pattern) (selected : d164070 q = 0) : d165311 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164070, d165311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14704 q selected
    | true =>
      simp only [d164070, d165311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14705 q selected
  have h10 (q : Pattern) (selected : d164071 q = 0) : d165367 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164071, d165367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d164071, d165367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164076 q = 0) : d165372 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164076, d165372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14706 q selected
    | true =>
      simp only [d164076, d165372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d164077 q = 0) : d165373 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164077, d165373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d164077, d165373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d164078 q = 0) : d165374 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164078, d165374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d164078, d165374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d164079 q = 0) : d165375 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164079, d165375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164079, d165375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d164080 q = 0) : d165376 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164080, d165376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164080, d165376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d164081 q = 0) : d165377 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d164081, d165377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164081, d165377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro14708 (p : Pattern) (selected : d164082 p = 0) : d165378 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163976 q = 0) : d165297 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163976, d165297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14685 q selected
    | true =>
      simp only [d163976, d165297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d163977 q = 0) : d165298 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163977, d165298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163977, d165298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163980 q = 0) : d165301 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163980, d165301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14686 q selected
    | true =>
      simp only [d163980, d165301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163981 q = 0) : d165302 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163981, d165302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163981, d165302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d163982 q = 0) : d165303 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d163982, d165303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163982, d165303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d163983 q = 0) : d165304 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d163983, d165304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d163983, d165304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164009 q = 0) : d165330 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164009, d165330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164009, d165330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164082 q = 0) : d165378 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164082, d165378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164082, d165378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14709 (p : Pattern) (selected : d164083 p = 0) : d165379 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163980 q = 0) : d165301 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163980, d165301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14686 q selected
    | true =>
      simp only [d163980, d165301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d163981 q = 0) : d165302 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163981, d165302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163981, d165302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163986 q = 0) : d165307 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d163986, d165307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163986, d165307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163987 q = 0) : d165308 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d163987, d165308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d163987, d165308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164011 q = 0) : d165332 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164011, d165332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164011, d165332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164083 q = 0) : d165379 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164083, d165379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164083, d165379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14710 (p : Pattern) (selected : d164088 p = 0) : d165384 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163976 q = 0) : d165297 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163976, d165297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14685 q selected
    | true =>
      simp only [d163976, d165297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d163977 q = 0) : d165298 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163977, d165298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163977, d165298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163980 q = 0) : d165301 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163980, d165301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14686 q selected
    | true =>
      simp only [d163980, d165301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163981 q = 0) : d165302 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163981, d165302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163981, d165302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d163982 q = 0) : d165303 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d163982, d165303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163982, d165303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164017 q = 0) : d165338 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164017, d165338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164017, d165338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164018 q = 0) : d165339 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164018, d165339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164018, d165339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164088 q = 0) : d165384 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164088, d165384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164088, d165384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14711 (p : Pattern) (selected : d164089 p = 0) : d165385 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163980 q = 0) : d165301 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163980, d165301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14686 q selected
    | true =>
      simp only [d163980, d165301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d163981 q = 0) : d165302 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163981, d165302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163981, d165302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163986 q = 0) : d165307 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d163986, d165307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163986, d165307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164020 q = 0) : d165341 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164020, d165341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164020, d165341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164021 q = 0) : d165342 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164021, d165342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164021, d165342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164089 q = 0) : d165385 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164089, d165385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164089, d165385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14712 (p : Pattern) (selected : d164093 p = 0) : d165389 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164039 q = 0) : d165360 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164039, d165360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14699 q selected
    | true =>
      simp only [d164039, d165360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164040 q = 0) : d165361 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164040, d165361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164040, d165361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163976 q = 0) : d165297 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163976, d165297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14685 q selected
    | true =>
      simp only [d163976, d165297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163977 q = 0) : d165298 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163977, d165298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163977, d165298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164041 q = 0) : d165362 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164041, d165362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164041, d165362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164042 q = 0) : d165363 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164042, d165363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164042, d165363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164043 q = 0) : d165364 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164043, d165364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164043, d165364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164093 q = 0) : d165389 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164093, d165389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164093, d165389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14713 (p : Pattern) (selected : d164095 p = 0) : d165319 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164056 q = 0) : d165297 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164056, d165297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14702 q selected
    | true =>
      simp only [d164056, d165297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164057 q = 0) : d165298 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164057, d165298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164057, d165298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164060 q = 0) : d165301 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164060, d165301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14703 q selected
    | true =>
      simp only [d164060, d165301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164061 q = 0) : d165302 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164061, d165302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164061, d165302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164062 q = 0) : d165303 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164062, d165303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164062, d165303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164063 q = 0) : d165304 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164063, d165304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164063, d165304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164064 q = 0) : d165305 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164064, d165305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164064, d165305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164095 q = 0) : d165319 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164095, d165319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164095, d165319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14714 (p : Pattern) (selected : d164096 p = 0) : d165320 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164060 q = 0) : d165301 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164060, d165301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14703 q selected
    | true =>
      simp only [d164060, d165301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164061 q = 0) : d165302 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164061, d165302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164061, d165302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164066 q = 0) : d165307 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164066, d165307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164066, d165307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164067 q = 0) : d165308 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164067, d165308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164067, d165308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164068 q = 0) : d165309 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164068, d165309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164068, d165309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164096 q = 0) : d165320 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164096, d165320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164096, d165320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14715 (p : Pattern) (selected : d164099 p = 0) : d165392 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163976 q = 0) : d165297 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163976, d165297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14685 q selected
    | true =>
      simp only [d163976, d165297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d163977 q = 0) : d165298 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163977, d165298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163977, d165298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164072 q = 0) : d165368 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164072, d165368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164072, d165368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164073 q = 0) : d165369 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164073, d165369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164073, d165369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164074 q = 0) : d165370 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164074, d165370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164074, d165370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164099 q = 0) : d165392 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164099, d165392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164099, d165392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14716 (p : Pattern) (selected : d164105 p = 0) : d165398 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164013 q = 0) : d165334 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164013, d165334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14693 q selected
    | true =>
      simp only [d164013, d165334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14694 q selected
  have h2 (q : Pattern) (selected : d164014 q = 0) : d165335 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164014, d165335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164014, d165335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164015 q = 0) : d165336 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164015, d165336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164015, d165336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164016 q = 0) : d165337 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164016, d165337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164016, d165337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164023 q = 0) : d165344 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164023, d165344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14695 q selected
    | true =>
      simp only [d164023, d165344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14696 q selected
  have h6 (q : Pattern) (selected : d164024 q = 0) : d165345 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164024, d165345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164024, d165345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164025 q = 0) : d165346 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164025, d165346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164025, d165346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164045 q = 0) : d165366 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164045, d165366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14700 q selected
    | true =>
      simp only [d164045, d165366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14687 q selected
  have h9 (q : Pattern) (selected : d164070 q = 0) : d165311 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164070, d165311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14704 q selected
    | true =>
      simp only [d164070, d165311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14705 q selected
  have h10 (q : Pattern) (selected : d164071 q = 0) : d165367 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164071, d165367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d164071, d165367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164076 q = 0) : d165372 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164076, d165372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14706 q selected
    | true =>
      simp only [d164076, d165372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d164077 q = 0) : d165373 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164077, d165373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d164077, d165373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d164078 q = 0) : d165374 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164078, d165374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d164078, d165374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d164079 q = 0) : d165375 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164079, d165375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164079, d165375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d164080 q = 0) : d165376 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164080, d165376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164080, d165376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d164084 q = 0) : d165380 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164084, d165380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14708 q selected
    | true =>
      simp only [d164084, d165380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14709 q selected
  have h17 (q : Pattern) (selected : d164085 q = 0) : d165381 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164085, d165381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164085, d165381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d164086 q = 0) : d165382 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164086, d165382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d164086, d165382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d164087 q = 0) : d165383 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164087, d165383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164087, d165383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d164090 q = 0) : d165386 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164090, d165386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14710 q selected
    | true =>
      simp only [d164090, d165386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14711 q selected
  have h21 (q : Pattern) (selected : d164091 q = 0) : d165387 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164091, d165387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164091, d165387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d164092 q = 0) : d165388 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164092, d165388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d164092, d165388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d164094 q = 0) : d165390 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164094, d165390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14712 q selected
    | true =>
      simp only [d164094, d165390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14690 q selected
  have h24 (q : Pattern) (selected : d164097 q = 0) : d165321 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164097, d165321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14713 q selected
    | true =>
      simp only [d164097, d165321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14714 q selected
  have h25 (q : Pattern) (selected : d164098 q = 0) : d165391 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164098, d165391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d164098, d165391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d164100 q = 0) : d165393 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164100, d165393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14715 q selected
    | true =>
      simp only [d164100, d165393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d164101 q = 0) : d165394 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164101, d165394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d164101, d165394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d164102 q = 0) : d165395 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164102, d165395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d164102, d165395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d164103 q = 0) : d165396 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164103, d165396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d164103, d165396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d164104 q = 0) : d165397 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164104, d165397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d164104, d165397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d164105 q = 0) : d165398 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d164105, d165398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d164105, d165398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro14717 (p : Pattern) (selected : d164112 p = 0) : d165405 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163990 q = 0) : d165311 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163990, d165311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14687 q selected
    | true =>
      simp only [d163990, d165311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14688 q selected
  have h2 (q : Pattern) (selected : d163991 q = 0) : d165312 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163991, d165312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163991, d165312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163992 q = 0) : d165313 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163992, d165313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163992, d165313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163993 q = 0) : d165314 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163993, d165314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163993, d165314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d163994 q = 0) : d165315 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163994, d165315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163994, d165315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164107 q = 0) : d165400 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164107, d165400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14688 q selected
    | true =>
      simp only [d164107, d165400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164108 q = 0) : d165401 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164108, d165401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164108, d165401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164109 q = 0) : d165402 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164109, d165402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164109, d165402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d164110 q = 0) : d165403 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164110, d165403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164110, d165403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d164111 q = 0) : d165404 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164111, d165404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164111, d165404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164112 q = 0) : d165405 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d164112, d165405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164112, d165405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14718 (p : Pattern) (selected : d164118 p = 0) : d165411 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164107 q = 0) : d165400 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164107, d165400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14688 q selected
    | true =>
      simp only [d164107, d165400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164108 q = 0) : d165401 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164108, d165401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164108, d165401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164109 q = 0) : d165402 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164109, d165402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164109, d165402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164110 q = 0) : d165403 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164110, d165403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164110, d165403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164111 q = 0) : d165404 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164111, d165404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164111, d165404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164113 q = 0) : d165406 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164113, d165406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14691 q selected
    | true =>
      simp only [d164113, d165406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164114 q = 0) : d165407 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164114, d165407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164114, d165407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164115 q = 0) : d165408 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164115, d165408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164115, d165408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d164116 q = 0) : d165409 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164116, d165409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164116, d165409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d164117 q = 0) : d165410 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164117, d165410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164117, d165410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164118 q = 0) : d165411 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d164118, d165411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164118, d165411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14719 (p : Pattern) (selected : d164125 p = 0) : d165418 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164094 q = 0) : d165390 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164094, d165390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14712 q selected
    | true =>
      simp only [d164094, d165390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14690 q selected
  have h2 (q : Pattern) (selected : d164097 q = 0) : d165321 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164097, d165321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14713 q selected
    | true =>
      simp only [d164097, d165321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14714 q selected
  have h3 (q : Pattern) (selected : d164098 q = 0) : d165391 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164098, d165391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d164098, d165391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164100 q = 0) : d165393 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164100, d165393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14715 q selected
    | true =>
      simp only [d164100, d165393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164101 q = 0) : d165394 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164101, d165394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164101, d165394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164102 q = 0) : d165395 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164102, d165395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164102, d165395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164123 q = 0) : d165416 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164123, d165416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164123, d165416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164124 q = 0) : d165417 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164124, d165417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164124, d165417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d164125 q = 0) : d165418 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d164125, d165418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164125, d165418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro14720 (p : Pattern) (selected : d164127 p = 0) : d165420 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164113 q = 0) : d165406 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164113, d165406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14691 q selected
    | true =>
      simp only [d164113, d165406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164114 q = 0) : d165407 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164114, d165407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164114, d165407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164115 q = 0) : d165408 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164115, d165408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164115, d165408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164116 q = 0) : d165409 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164116, d165409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164116, d165409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164117 q = 0) : d165410 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164117, d165410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164117, d165410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164127 q = 0) : d165420 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d164127, d165420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164127, d165420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14721 (p : Pattern) (selected : d164134 p = 0) : d165427 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d163996 q = 0) : d165317 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163996, d165317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163996, d165317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14689 q selected
  have h2 (q : Pattern) (selected : d163997 q = 0) : d165318 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163997, d165318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d163997, d165318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d164006 q = 0) : d165327 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d164006, d165327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14689 q selected
    | true =>
      simp only [d164006, d165327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14692 q selected
  have h4 (q : Pattern) (selected : d164007 q = 0) : d165328 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d164007, d165328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164007, d165328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164008 q = 0) : d165329 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d164008, d165329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164008, d165329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164106 q = 0) : d165399 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d164106, d165399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14707 q selected
    | true =>
      simp only [d164106, d165399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14716 q selected
  have h7 (q : Pattern) (selected : d164119 q = 0) : d165412 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d164119, d165412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14717 q selected
    | true =>
      simp only [d164119, d165412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14718 q selected
  have h8 (q : Pattern) (selected : d164120 q = 0) : d165413 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d164120, d165413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164120, d165413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d164121 q = 0) : d165414 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d164121, d165414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d164121, d165414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d164122 q = 0) : d165415 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d164122, d165415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164122, d165415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164126 q = 0) : d165419 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d164126, d165419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164126, d165419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14719 q selected
  have h12 (q : Pattern) (selected : d164128 q = 0) : d165421 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d164128, d165421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164128, d165421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14720 q selected
  have h13 (q : Pattern) (selected : d164129 q = 0) : d165422 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d164129, d165422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d164129, d165422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d164130 q = 0) : d165423 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d164130, d165423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d164130, d165423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d164131 q = 0) : d165424 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d164131, d165424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d164131, d165424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d164132 q = 0) : d165425 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d164132, d165425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d164132, d165425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d164133 q = 0) : d165426 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d164133, d165426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d164133, d165426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d164134 q = 0) : d165427 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d164134, d165427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d164134, d165427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro14722 (p : Pattern) (selected : d164140 p = 0) : d165433 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164135 q = 0) : d165428 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d164135, d165428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164135, d165428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14721 q selected
  have h2 (q : Pattern) (selected : d164136 q = 0) : d165429 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d164136, d165429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164136, d165429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164137 q = 0) : d165430 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d164137, d165430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164137, d165430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164138 q = 0) : d165431 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d164138, d165431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164138, d165431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164139 q = 0) : d165432 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d164139, d165432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164139, d165432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164140 q = 0) : d165433 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d164140, d165433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164140, d165433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14723 (p : Pattern) (selected : d164143 p = 0) : d165436 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d543 q = 0) : d52290 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro277 q selected
    | true =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d544 q = 0) : d52291 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d9458 q = 0) : d101073 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9458, d101073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6619 q selected
    | true =>
      simp only [d9458, d101073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d9460 q = 0) : d101075 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9460, d101075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d9460, d101075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164026 q = 0) : d165347 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164026, d165347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164026, d165347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9468 q = 0) : d101083 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6620 q selected
    | true =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d9470 q = 0) : d101085 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d751 q = 0) : d52428 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro317 q selected
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d752 q = 0) : d52429 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d164142 q = 0) : d165435 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164142, d165435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164142, d165435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164143 q = 0) : d165436 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164143, d165436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164143, d165436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14724 (p : Pattern) (selected : d164146 p = 0) : d165439 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d319 q = 0) : d52118 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro235 q selected
    | true =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d320 q = 0) : d52119 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d751 q = 0) : d52428 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro317 q selected
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d752 q = 0) : d52429 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164144 q = 0) : d165437 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164144, d165437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164144, d165437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164145 q = 0) : d165438 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164145, d165438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164145, d165438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164146 q = 0) : d165439 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164146, d165439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164146, d165439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro14725 (p : Pattern) (selected : d164150 p = 0) : d165443 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d751 q = 0) : d52428 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro317 q selected
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d752 q = 0) : d52429 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d164145 q = 0) : d165438 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164145, d165438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164145, d165438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164150 q = 0) : d165443 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164150, d165443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164150, d165443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro14726 (p : Pattern) (selected : d164157 p = 0) : d165450 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164147 q = 0) : d165440 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164147, d165440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14723 q selected
    | true =>
      simp only [d164147, d165440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14724 q selected
  have h2 (q : Pattern) (selected : d164148 q = 0) : d165441 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164148, d165441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164148, d165441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164149 q = 0) : d165442 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164149, d165442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164149, d165442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164151 q = 0) : d165444 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164151, d165444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14724 q selected
    | true =>
      simp only [d164151, d165444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14725 q selected
  have h5 (q : Pattern) (selected : d164152 q = 0) : d165445 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164152, d165445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164152, d165445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164153 q = 0) : d165446 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164153, d165446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164153, d165446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164154 q = 0) : d165447 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164154, d165447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164154, d165447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164155 q = 0) : d165448 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164155, d165448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164155, d165448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d164156 q = 0) : d165449 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d164156, d165449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164156, d165449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d164157 q = 0) : d165450 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d164157, d165450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d164157, d165450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro14727 (p : Pattern) (selected : d164161 p = 0) : d165454 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164151 q = 0) : d165444 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164151, d165444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14724 q selected
    | true =>
      simp only [d164151, d165444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14725 q selected
  have h2 (q : Pattern) (selected : d164152 q = 0) : d165445 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164152, d165445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164152, d165445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164153 q = 0) : d165446 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164153, d165446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164153, d165446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164155 q = 0) : d165448 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164155, d165448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164155, d165448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164160 q = 0) : d165453 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d164160, d165453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164160, d165453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164161 q = 0) : d165454 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d164161, d165454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164161, d165454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14728 (p : Pattern) (selected : d164167 p = 0) : d165460 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164158 q = 0) : d165451 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164158, d165451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14726 q selected
    | true =>
      simp only [d164158, d165451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164159 q = 0) : d165452 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164159, d165452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164159, d165452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164162 q = 0) : d165455 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164162, d165455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14727 q selected
    | true =>
      simp only [d164162, d165455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164163 q = 0) : d165456 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164163, d165456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164163, d165456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164164 q = 0) : d165457 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164164, d165457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164164, d165457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164165 q = 0) : d165458 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164165, d165458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164165, d165458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164166 q = 0) : d165459 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164166, d165459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164166, d165459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164167 q = 0) : d165460 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164167, d165460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164167, d165460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14729 (p : Pattern) (selected : d164171 p = 0) : d165464 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164162 q = 0) : d165455 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164162, d165455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14727 q selected
    | true =>
      simp only [d164162, d165455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164163 q = 0) : d165456 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164163, d165456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164163, d165456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164168 q = 0) : d165461 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164168, d165461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164168, d165461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164169 q = 0) : d165462 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164169, d165462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164169, d165462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164170 q = 0) : d165463 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164170, d165463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164170, d165463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164171 q = 0) : d165464 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164171, d165464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164171, d165464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14730 (p : Pattern) (selected : d164177 p = 0) : d165470 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164172 q = 0) : d165465 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164172, d165465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14728 q selected
    | true =>
      simp only [d164172, d165465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14729 q selected
  have h2 (q : Pattern) (selected : d164173 q = 0) : d165466 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164173, d165466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164173, d165466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164174 q = 0) : d165467 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164174, d165467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164174, d165467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164175 q = 0) : d165468 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164175, d165468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164175, d165468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164176 q = 0) : d165469 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164176, d165469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164176, d165469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164177 q = 0) : d165470 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d164177, d165470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164177, d165470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14731 (p : Pattern) (selected : d164180 p = 0) : d165473 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164158 q = 0) : d165451 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164158, d165451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14726 q selected
    | true =>
      simp only [d164158, d165451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164159 q = 0) : d165452 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164159, d165452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164159, d165452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164162 q = 0) : d165455 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164162, d165455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14727 q selected
    | true =>
      simp only [d164162, d165455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164163 q = 0) : d165456 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164163, d165456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164163, d165456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164164 q = 0) : d165457 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164164, d165457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164164, d165457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164165 q = 0) : d165458 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164165, d165458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164165, d165458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164166 q = 0) : d165459 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164166, d165459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164166, d165459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164180 q = 0) : d165473 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164180, d165473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164180, d165473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14732 (p : Pattern) (selected : d164181 p = 0) : d165474 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164162 q = 0) : d165455 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164162, d165455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14727 q selected
    | true =>
      simp only [d164162, d165455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164163 q = 0) : d165456 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164163, d165456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164163, d165456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164168 q = 0) : d165461 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164168, d165461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164168, d165461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164169 q = 0) : d165462 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164169, d165462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164169, d165462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164170 q = 0) : d165463 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164170, d165463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164170, d165463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164181 q = 0) : d165474 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164181, d165474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164181, d165474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14733 (p : Pattern) (selected : d164187 p = 0) : d165480 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164172 q = 0) : d165465 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164172, d165465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14728 q selected
    | true =>
      simp only [d164172, d165465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14729 q selected
  have h2 (q : Pattern) (selected : d164173 q = 0) : d165466 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164173, d165466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164173, d165466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164174 q = 0) : d165467 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164174, d165467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164174, d165467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164175 q = 0) : d165468 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164175, d165468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164175, d165468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164176 q = 0) : d165469 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164176, d165469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164176, d165469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164182 q = 0) : d165475 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164182, d165475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14731 q selected
    | true =>
      simp only [d164182, d165475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14732 q selected
  have h7 (q : Pattern) (selected : d164183 q = 0) : d165476 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164183, d165476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164183, d165476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164184 q = 0) : d165477 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164184, d165477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164184, d165477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d164185 q = 0) : d165478 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164185, d165478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164185, d165478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d164186 q = 0) : d165479 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164186, d165479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164186, d165479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164187 q = 0) : d165480 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d164187, d165480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164187, d165480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14734 (p : Pattern) (selected : d164192 p = 0) : d165485 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164158 q = 0) : d165451 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164158, d165451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14726 q selected
    | true =>
      simp only [d164158, d165451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164159 q = 0) : d165452 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164159, d165452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164159, d165452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164162 q = 0) : d165455 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164162, d165455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14727 q selected
    | true =>
      simp only [d164162, d165455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164163 q = 0) : d165456 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164163, d165456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164163, d165456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164164 q = 0) : d165457 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164164, d165457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164164, d165457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164165 q = 0) : d165458 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164165, d165458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164165, d165458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164191 q = 0) : d165484 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164191, d165484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164191, d165484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164192 q = 0) : d165485 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164192, d165485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164192, d165485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14735 (p : Pattern) (selected : d164194 p = 0) : d165487 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164162 q = 0) : d165455 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164162, d165455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14727 q selected
    | true =>
      simp only [d164162, d165455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164163 q = 0) : d165456 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164163, d165456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164163, d165456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164168 q = 0) : d165461 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164168, d165461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164168, d165461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164169 q = 0) : d165462 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164169, d165462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164169, d165462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164193 q = 0) : d165486 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164193, d165486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164193, d165486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164194 q = 0) : d165487 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164194, d165487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164194, d165487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14736 (p : Pattern) (selected : d164201 p = 0) : d165494 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164158 q = 0) : d165451 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164158, d165451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14726 q selected
    | true =>
      simp only [d164158, d165451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164159 q = 0) : d165452 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164159, d165452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164159, d165452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164162 q = 0) : d165455 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164162, d165455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14727 q selected
    | true =>
      simp only [d164162, d165455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164163 q = 0) : d165456 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164163, d165456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164163, d165456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164164 q = 0) : d165457 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164164, d165457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164164, d165457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164199 q = 0) : d165492 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164199, d165492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164199, d165492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164200 q = 0) : d165493 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164200, d165493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164200, d165493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164201 q = 0) : d165494 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164201, d165494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164201, d165494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14737 (p : Pattern) (selected : d164204 p = 0) : d165497 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164162 q = 0) : d165455 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164162, d165455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14727 q selected
    | true =>
      simp only [d164162, d165455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164163 q = 0) : d165456 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164163, d165456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164163, d165456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164168 q = 0) : d165461 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164168, d165461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164168, d165461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164202 q = 0) : d165495 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164202, d165495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164202, d165495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164203 q = 0) : d165496 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164203, d165496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164203, d165496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164204 q = 0) : d165497 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164204, d165497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164204, d165497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14738 (p : Pattern) (selected : d164210 p = 0) : d165503 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d834 q = 0) : d52511 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d834, d52511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro335 q selected
    | true =>
      simp only [d834, d52511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d835 q = 0) : d52512 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d835, d52512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d835, d52512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d9587 q = 0) : d101167 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9587, d101167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6641 q selected
    | true =>
      simp only [d9587, d101167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d9589 q = 0) : d101169 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9589, d101169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d9589, d101169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164208 q = 0) : d165501 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164208, d165501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164208, d165501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9597 q = 0) : d101177 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9597, d101177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6642 q selected
    | true =>
      simp only [d9597, d101177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d9599 q = 0) : d101179 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9599, d101179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9599, d101179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d9468 q = 0) : d101083 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6620 q selected
    | true =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d9470 q = 0) : d101085 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d164209 q = 0) : d165502 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164209, d165502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164209, d165502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164210 q = 0) : d165503 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164210, d165503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164210, d165503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14739 (p : Pattern) (selected : d164214 p = 0) : d165507 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d9468 q = 0) : d101083 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6620 q selected
    | true =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9470 q = 0) : d101085 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d751 q = 0) : d52428 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro317 q selected
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d752 q = 0) : d52429 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164142 q = 0) : d165435 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164142, d165435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164142, d165435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164145 q = 0) : d165438 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164145, d165438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164145, d165438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164214 q = 0) : d165507 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164214, d165507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164214, d165507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro14740 (p : Pattern) (selected : d164220 p = 0) : d165513 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164211 q = 0) : d165504 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164211, d165504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14738 q selected
    | true =>
      simp only [d164211, d165504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14723 q selected
  have h2 (q : Pattern) (selected : d164212 q = 0) : d165505 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164212, d165505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164212, d165505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164213 q = 0) : d165506 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164213, d165506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164213, d165506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164215 q = 0) : d165508 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164215, d165508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14723 q selected
    | true =>
      simp only [d164215, d165508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14739 q selected
  have h5 (q : Pattern) (selected : d164216 q = 0) : d165509 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164216, d165509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164216, d165509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164217 q = 0) : d165510 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164217, d165510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164217, d165510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164218 q = 0) : d165511 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164218, d165511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164218, d165511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164147 q = 0) : d165440 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164147, d165440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14723 q selected
    | true =>
      simp only [d164147, d165440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14724 q selected
  have h9 (q : Pattern) (selected : d164148 q = 0) : d165441 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164148, d165441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164148, d165441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d164149 q = 0) : d165442 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164149, d165442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164149, d165442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164151 q = 0) : d165444 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164151, d165444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14724 q selected
    | true =>
      simp only [d164151, d165444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14725 q selected
  have h12 (q : Pattern) (selected : d164152 q = 0) : d165445 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164152, d165445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164152, d165445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d164153 q = 0) : d165446 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164153, d165446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164153, d165446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d164154 q = 0) : d165447 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164154, d165447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d164154, d165447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d164219 q = 0) : d165512 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d164219, d165512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164219, d165512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d164220 q = 0) : d165513 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d164220, d165513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d164220, d165513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro14741 (p : Pattern) (selected : d164226 p = 0) : d165519 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164221 q = 0) : d165514 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164221, d165514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14740 q selected
    | true =>
      simp only [d164221, d165514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164222 q = 0) : d165515 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164222, d165515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164222, d165515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164158 q = 0) : d165451 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164158, d165451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14726 q selected
    | true =>
      simp only [d164158, d165451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164159 q = 0) : d165452 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164159, d165452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164159, d165452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164223 q = 0) : d165516 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164223, d165516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164223, d165516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164224 q = 0) : d165517 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164224, d165517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164224, d165517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164225 q = 0) : d165518 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164225, d165518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164225, d165518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164226 q = 0) : d165519 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164226, d165519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164226, d165519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14742 (p : Pattern) (selected : d164230 p = 0) : d165436 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d868 q = 0) : d52290 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d868, d52290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro341 q selected
    | true =>
      simp only [d868, d52290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d869 q = 0) : d52291 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d869, d52291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d869, d52291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d9661 q = 0) : d101073 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9661, d101073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6654 q selected
    | true =>
      simp only [d9661, d101073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d9663 q = 0) : d101075 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9663, d101075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d9663, d101075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164228 q = 0) : d165347 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164228, d165347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164228, d165347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9671 q = 0) : d101083 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9671, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6655 q selected
    | true =>
      simp only [d9671, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d9673 q = 0) : d101085 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9673, d101085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9673, d101085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d874 q = 0) : d52428 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d874, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro342 q selected
    | true =>
      simp only [d874, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d875 q = 0) : d52429 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d875, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d875, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d164229 q = 0) : d165435 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164229, d165435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164229, d165435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164230 q = 0) : d165436 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164230, d165436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164230, d165436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14743 (p : Pattern) (selected : d164233 p = 0) : d165439 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d574 q = 0) : d52118 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d574, d52118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro282 q selected
    | true =>
      simp only [d574, d52118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d575 q = 0) : d52119 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d575, d52119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d575, d52119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d874 q = 0) : d52428 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d874, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro342 q selected
    | true =>
      simp only [d874, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d875 q = 0) : d52429 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d875, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d875, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164231 q = 0) : d165437 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164231, d165437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164231, d165437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164232 q = 0) : d165438 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164232, d165438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164232, d165438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164233 q = 0) : d165439 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164233, d165439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164233, d165439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro14744 (p : Pattern) (selected : d164237 p = 0) : d165443 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d874 q = 0) : d52428 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d874, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro342 q selected
    | true =>
      simp only [d874, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d875 q = 0) : d52429 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d875, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d875, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d164232 q = 0) : d165438 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164232, d165438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164232, d165438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164237 q = 0) : d165443 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164237, d165443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164237, d165443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro14745 (p : Pattern) (selected : d164244 p = 0) : d165450 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164234 q = 0) : d165440 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164234, d165440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14742 q selected
    | true =>
      simp only [d164234, d165440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14743 q selected
  have h2 (q : Pattern) (selected : d164235 q = 0) : d165441 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164235, d165441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164235, d165441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164236 q = 0) : d165442 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164236, d165442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164236, d165442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164238 q = 0) : d165444 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164238, d165444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14743 q selected
    | true =>
      simp only [d164238, d165444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14744 q selected
  have h5 (q : Pattern) (selected : d164239 q = 0) : d165445 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164239, d165445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164239, d165445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164240 q = 0) : d165446 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164240, d165446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164240, d165446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164241 q = 0) : d165447 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164241, d165447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164241, d165447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164242 q = 0) : d165448 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164242, d165448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164242, d165448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d164243 q = 0) : d165449 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d164243, d165449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164243, d165449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d164244 q = 0) : d165450 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d164244, d165450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d164244, d165450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro14746 (p : Pattern) (selected : d164248 p = 0) : d165454 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164238 q = 0) : d165444 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164238, d165444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14743 q selected
    | true =>
      simp only [d164238, d165444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14744 q selected
  have h2 (q : Pattern) (selected : d164239 q = 0) : d165445 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164239, d165445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164239, d165445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164240 q = 0) : d165446 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164240, d165446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164240, d165446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164242 q = 0) : d165448 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164242, d165448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164242, d165448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164247 q = 0) : d165453 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d164247, d165453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164247, d165453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164248 q = 0) : d165454 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d164248, d165454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164248, d165454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14747 (p : Pattern) (selected : d164254 p = 0) : d165460 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164245 q = 0) : d165451 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164245, d165451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14745 q selected
    | true =>
      simp only [d164245, d165451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164246 q = 0) : d165452 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164246, d165452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164246, d165452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164249 q = 0) : d165455 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164249, d165455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14746 q selected
    | true =>
      simp only [d164249, d165455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164250 q = 0) : d165456 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164250, d165456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164250, d165456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164251 q = 0) : d165457 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164251, d165457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164251, d165457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164252 q = 0) : d165458 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164252, d165458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164252, d165458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164253 q = 0) : d165459 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164253, d165459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164253, d165459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164254 q = 0) : d165460 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164254, d165460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164254, d165460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14748 (p : Pattern) (selected : d164258 p = 0) : d165464 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164249 q = 0) : d165455 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164249, d165455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14746 q selected
    | true =>
      simp only [d164249, d165455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164250 q = 0) : d165456 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164250, d165456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164250, d165456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164255 q = 0) : d165461 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164255, d165461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164255, d165461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164256 q = 0) : d165462 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164256, d165462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164256, d165462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164257 q = 0) : d165463 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164257, d165463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164257, d165463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164258 q = 0) : d165464 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164258, d165464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164258, d165464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14749 (p : Pattern) (selected : d164264 p = 0) : d165525 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164158 q = 0) : d165451 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164158, d165451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14726 q selected
    | true =>
      simp only [d164158, d165451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164159 q = 0) : d165452 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164159, d165452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164159, d165452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164261 q = 0) : d165522 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164261, d165522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164261, d165522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164262 q = 0) : d165523 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164262, d165523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164262, d165523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164263 q = 0) : d165524 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164263, d165524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164263, d165524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164264 q = 0) : d165525 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164264, d165525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164264, d165525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
end NetHack.Soko22Hazard87
