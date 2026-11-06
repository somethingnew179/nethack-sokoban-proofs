import NetHack.Soko22Hazard87.EqIntroBlocks0063
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro16000 (p : Pattern) (selected : d174432 p = 1) : d175856 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d174416 q = 1) : d175851 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d174416, d175851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174416, d175851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15999 q selected
  have h2 (q : Pattern) (selected : d174427 q = 1) : d174427 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d174428 q = 1) : d175852 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d174428, d175852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174428, d175852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174429 q = 1) : d175853 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d174429, d175853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174429, d175853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174430 q = 1) : d175854 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d174430, d175854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174430, d175854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174431 q = 1) : d175855 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d174431, d175855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174431, d175855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174432 q = 1) : d175856 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d174432, d175856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174432, d175856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16001 (p : Pattern) (selected : d174438 p = 1) : d175862 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d174433 q = 1) : d175857 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d174433, d175857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174433, d175857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16000 q selected
  have h2 (q : Pattern) (selected : d174434 q = 1) : d175858 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d174434, d175858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174434, d175858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174435 q = 1) : d175859 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d174435, d175859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174435, d175859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174436 q = 1) : d175860 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d174436, d175860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174436, d175860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d174437 q = 1) : d175861 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d174437, d175861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174437, d175861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174438 q = 1) : d175862 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d174438, d175862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174438, d175862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16002 (p : Pattern) (selected : d174515 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2201 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro148 q selected
    | true =>
      simp only [d2201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174509 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d10458 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6872 q selected
    | true =>
      simp only [d10458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174510 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174511 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10468 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6873 q selected
    | true =>
      simp only [d10468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174512 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d174512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10482 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6874 q selected
    | true =>
      simp only [d10482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d174513 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d174513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d174514 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d174515 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16003 (p : Pattern) (selected : d174520 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2219 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro153 q selected
    | true =>
      simp only [d2219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174516 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d10493 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6876 q selected
    | true =>
      simp only [d10493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174517 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174518 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10482 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6874 q selected
    | true =>
      simp only [d10482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174513 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d174513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d174519 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d174520 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro16004 (p : Pattern) (selected : d174528 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d10508 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6878 q selected
    | true =>
      simp only [d10508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174524 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d174525 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10521 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6879 q selected
    | true =>
      simp only [d10521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174526 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174527 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174528 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16005 (p : Pattern) (selected : d174535 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2231 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro154 q selected
    | true =>
      simp only [d2231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174533 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d174534 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10521 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6879 q selected
    | true =>
      simp only [d10521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174526 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174527 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174535 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16006 (p : Pattern) (selected : d174541 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d174521 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16002 q selected
    | true =>
      simp only [d174521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16003 q selected
  have h2 (q : Pattern) (selected : d174522 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174523 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174529 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16003 q selected
    | true =>
      simp only [d174529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16004 q selected
  have h5 (q : Pattern) (selected : d174530 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174531 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d174532 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d174536 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16003 q selected
    | true =>
      simp only [d174536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16005 q selected
  have h9 (q : Pattern) (selected : d174537 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d174538 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d174539 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d174539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d174540 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d174541 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d174541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d174541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro16007 (p : Pattern) (selected : d174545 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d174536 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16003 q selected
    | true =>
      simp only [d174536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16005 q selected
  have h2 (q : Pattern) (selected : d174537 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174538 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174539 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174544 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174545 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d174545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16008 (p : Pattern) (selected : d174551 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d174542 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d174542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16006 q selected
    | true =>
      simp only [d174542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174543 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d174543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174546 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d174546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16007 q selected
    | true =>
      simp only [d174546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174547 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d174547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d174548 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d174548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174549 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d174549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174550 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d174550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d174550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d174551 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d174551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16009 (p : Pattern) (selected : d174555 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d174546 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d174546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16007 q selected
    | true =>
      simp only [d174546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174547 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d174547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174552 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d174552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174553 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d174553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174554 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d174554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174555 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d174555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16010 (p : Pattern) (selected : d174576 p = 1) : d175871 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d174508 q = 1) : d174508 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d174556 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d174556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16008 q selected
    | true =>
      simp only [d174556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16009 q selected
  have h3 (q : Pattern) (selected : d174557 q = 1) : d175867 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d174557, d175867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174557, d175867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174572 q = 1) : d174572 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d174573 q = 1) : d175868 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d174573, d175868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174573, d175868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174574 q = 1) : d175869 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d174574, d175869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174574, d175869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d174575 q = 1) : d175870 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d174575, d175870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174575, d175870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d174576 q = 1) : d175871 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d174576, d175871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174576, d175871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16011 (p : Pattern) (selected : d174593 p = 1) : d175877 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d174577 q = 1) : d175872 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d174577, d175872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174577, d175872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16010 q selected
  have h2 (q : Pattern) (selected : d174588 q = 1) : d174588 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d174589 q = 1) : d175873 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d174589, d175873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174589, d175873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174590 q = 1) : d175874 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d174590, d175874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174590, d175874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174591 q = 1) : d175875 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d174591, d175875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174591, d175875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174592 q = 1) : d175876 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d174592, d175876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174592, d175876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174593 q = 1) : d175877 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d174593, d175877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174593, d175877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16012 (p : Pattern) (selected : d174599 p = 1) : d175883 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d174594 q = 1) : d175878 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d174594, d175878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174594, d175878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16011 q selected
  have h2 (q : Pattern) (selected : d174595 q = 1) : d175879 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d174595, d175879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174595, d175879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174596 q = 1) : d175880 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d174596, d175880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174596, d175880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174597 q = 1) : d175881 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d174597, d175881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174597, d175881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d174598 q = 1) : d175882 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d174598, d175882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174598, d175882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174599 q = 1) : d175883 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d174599, d175883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174599, d175883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16013 (p : Pattern) (selected : d174605 p = 1) : d175889 p = 1 := by
  have h0 (q : Pattern) (selected : d173995 q = 1) : d175806 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d173995, d175806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15961 q selected
    | true =>
      simp only [d173995, d175806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15969 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d174116 q = 1) : d175824 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d174116, d175824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174116, d175824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15979 q selected
  have h3 (q : Pattern) (selected : d174117 q = 1) : d175825 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d174117, d175825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174117, d175825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174276 q = 1) : d175843 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d174276, d175843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174276, d175843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15990 q selected
  have h5 (q : Pattern) (selected : d174277 q = 1) : d175844 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d174277, d175844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174277, d175844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174278 q = 1) : d175845 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d174278, d175845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174278, d175845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d174439 q = 1) : d175863 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d174439, d175863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174439, d175863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16001 q selected
  have h8 (q : Pattern) (selected : d174440 q = 1) : d175864 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d174440, d175864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174440, d175864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d174441 q = 1) : d175865 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d174441, d175865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174441, d175865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d174442 q = 1) : d175866 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d174442, d175866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d174442, d175866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d174600 q = 1) : d175884 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d174600, d175884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174600, d175884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16012 q selected
  have h12 (q : Pattern) (selected : d174601 q = 1) : d175885 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d174601, d175885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174601, d175885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d174602 q = 1) : d175886 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d174602, d175886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174602, d175886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d174603 q = 1) : d175887 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d174603, d175887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174603, d175887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d174604 q = 1) : d175888 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d174604, d175888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d174604, d175888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d174605 q = 1) : d175889 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d174605, d175889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d174605, d175889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro16014 (p : Pattern) (selected : d174611 p = 1) : d175895 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d174606 q = 1) : d175890 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d174606, d175890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16013 q selected
    | true =>
      simp only [d174606, d175890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174607 q = 1) : d175891 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d174607, d175891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174607, d175891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d174608 q = 1) : d175892 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d174608, d175892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174608, d175892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174609 q = 1) : d175893 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d174609, d175893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174609, d175893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174610 q = 1) : d175894 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d174610, d175894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174610, d175894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174611 q = 1) : d175895 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d174611, d175895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174611, d175895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16015 (p : Pattern) (selected : d174617 p = 1) : d175901 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d174612 q = 1) : d175896 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d174612, d175896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16014 q selected
    | true =>
      simp only [d174612, d175896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174613 q = 1) : d175897 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d174613, d175897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174613, d175897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d174614 q = 1) : d175898 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d174614, d175898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174614, d175898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174615 q = 1) : d175899 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d174615, d175899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174615, d175899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174616 q = 1) : d175900 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d174616, d175900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174616, d175900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174617 q = 1) : d175901 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d174617, d175901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174617, d175901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16016 (p : Pattern) (selected : d174623 p = 1) : d175907 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d174618 q = 1) : d175902 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d174618, d175902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16015 q selected
    | true =>
      simp only [d174618, d175902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174619 q = 1) : d175903 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d174619, d175903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174619, d175903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d174620 q = 1) : d175904 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d174620, d175904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174620, d175904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174621 q = 1) : d175905 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d174621, d175905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174621, d175905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174622 q = 1) : d175906 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d174622, d175906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174622, d175906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174623 q = 1) : d175907 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d174623, d175907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174623, d175907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16017 (p : Pattern) (selected : d174629 p = 1) : d175913 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d174624 q = 1) : d175908 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d174624, d175908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16016 q selected
    | true =>
      simp only [d174624, d175908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174625 q = 1) : d175909 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d174625, d175909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174625, d175909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d174626 q = 1) : d175910 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d174626, d175910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174626, d175910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174627 q = 1) : d175911 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d174627, d175911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174627, d175911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174628 q = 1) : d175912 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d174628, d175912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174628, d175912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174629 q = 1) : d175913 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d174629, d175913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174629, d175913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16018 (p : Pattern) (selected : d174635 p = 1) : d175919 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d174630 q = 1) : d175914 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d174630, d175914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16017 q selected
    | true =>
      simp only [d174630, d175914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174631 q = 1) : d175915 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d174631, d175915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174631, d175915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d174632 q = 1) : d175916 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d174632, d175916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174632, d175916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174633 q = 1) : d175917 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d174633, d175917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174633, d175917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174634 q = 1) : d175918 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d174634, d175918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174634, d175918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174635 q = 1) : d175919 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d174635, d175919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174635, d175919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16019 (p : Pattern) (selected : d174641 p = 1) : d175925 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d174636 q = 1) : d175920 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d174636, d175920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16018 q selected
    | true =>
      simp only [d174636, d175920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174637 q = 1) : d175921 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d174637, d175921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174637, d175921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d174638 q = 1) : d175922 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d174638, d175922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174638, d175922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174639 q = 1) : d175923 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d174639, d175923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174639, d175923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174640 q = 1) : d175924 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d174640, d175924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174640, d175924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174641 q = 1) : d175925 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d174641, d175925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174641, d175925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16020 (p : Pattern) (selected : d174647 p = 1) : d175931 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d174642 q = 1) : d175926 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d174642, d175926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16019 q selected
    | true =>
      simp only [d174642, d175926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174643 q = 1) : d175927 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d174643, d175927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174643, d175927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d174644 q = 1) : d175928 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d174644, d175928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174644, d175928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174645 q = 1) : d175929 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d174645, d175929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174645, d175929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174646 q = 1) : d175930 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d174646, d175930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174646, d175930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174647 q = 1) : d175931 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d174647, d175931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174647, d175931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16021 (p : Pattern) (selected : d12494 p = 0) : d112928 p = 1 := by
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
  have h3 (q : Pattern) (selected : d12493 q = 0) : d112927 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, d112927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12493, d112927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d12494 q = 0) : d112928 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, d112928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12494, d112928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16022 (p : Pattern) (selected : d175937 p = 0) : d177189 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d175932 q = 0) : d177184 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d175932, d177184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16021 q selected
    | true =>
      simp only [d175932, d177184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12344 q selected
  have h2 (q : Pattern) (selected : d175933 q = 0) : d177185 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d175933, d177185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d175933, d177185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d175934 q = 0) : d177186 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d175934, d177186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d175934, d177186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d142667 q = 0) : d144104 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d142667, d144104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12344 q selected
    | true =>
      simp only [d142667, d144104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d142668 q = 0) : d144105 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d142668, d144105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142668, d144105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142669 q = 0) : d144106 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d142669, d144106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142669, d144106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d175935 q = 0) : d177187 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d175935, d177187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d175935, d177187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d142670 q = 0) : d144107 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d142670, d144107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d142670, d144107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d175936 q = 0) : d177188 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d175936, d177188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d175936, d177188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d175937 q = 0) : d177189 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d175937, d177189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d175937, d177189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16023 (p : Pattern) (selected : d175943 p = 0) : d177195 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d175938 q = 0) : d177190 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d175938, d177190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16022 q selected
    | true =>
      simp only [d175938, d177190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d175939 q = 0) : d177191 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d175939, d177191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d175939, d177191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142673 q = 0) : d144110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142673, d144110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12345 q selected
    | true =>
      simp only [d142673, d144110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142674 q = 0) : d144111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142674, d144111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142674, d144111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d175940 q = 0) : d177192 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d175940, d177192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d175940, d177192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d175941 q = 0) : d177193 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d175941, d177193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d175941, d177193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d175942 q = 0) : d177194 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d175942, d177194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d175942, d177194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d175943 q = 0) : d177195 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d175943, d177195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d175943, d177195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16024 (p : Pattern) (selected : d175949 p = 0) : d177201 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142748 q = 0) : d144185 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142748, d144185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12358 q selected
    | true =>
      simp only [d142748, d144185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d142749 q = 0) : d144186 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142749, d144186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142749, d144186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142750 q = 0) : d144187 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142750, d144187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142750, d144187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142751 q = 0) : d144188 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d142751, d144188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142751, d144188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d142755 q = 0) : d144192 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142755, d144192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12359 q selected
    | true =>
      simp only [d142755, d144192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d142756 q = 0) : d144193 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142756, d144193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142756, d144193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d142757 q = 0) : d144194 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142757, d144194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d142757, d144194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d175944 q = 0) : d177196 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d175944, d177196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16023 q selected
    | true =>
      simp only [d175944, d177196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12346 q selected
  have h9 (q : Pattern) (selected : d142783 q = 0) : d144116 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142783, d144116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12365 q selected
    | true =>
      simp only [d142783, d144116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d175945 q = 0) : d177197 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d175945, d177197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d175945, d177197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d142679 q = 0) : d144116 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142679, d144116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12346 q selected
    | true =>
      simp only [d142679, d144116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d142680 q = 0) : d144117 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142680, d144117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d142680, d144117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d175946 q = 0) : d177198 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d175946, d177198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d175946, d177198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d175947 q = 0) : d177199 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d175947, d177199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d175947, d177199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d175948 q = 0) : d177200 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d175948, d177200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d175948, d177200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d175949 q = 0) : d177201 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d175949, d177201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d175949, d177201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro16025 (p : Pattern) (selected : d175950 p = 0) : d177202 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d175938 q = 0) : d177190 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d175938, d177190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16022 q selected
    | true =>
      simp only [d175938, d177190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d175939 q = 0) : d177191 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d175939, d177191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d175939, d177191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142673 q = 0) : d144110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142673, d144110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12345 q selected
    | true =>
      simp only [d142673, d144110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142674 q = 0) : d144111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142674, d144111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142674, d144111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d175940 q = 0) : d177192 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d175940, d177192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d175940, d177192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d175941 q = 0) : d177193 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d175941, d177193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d175941, d177193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d175942 q = 0) : d177194 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d175942, d177194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d175942, d177194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d175950 q = 0) : d177202 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d175950, d177202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d175950, d177202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16026 (p : Pattern) (selected : d175956 p = 0) : d177208 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142748 q = 0) : d144185 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142748, d144185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12358 q selected
    | true =>
      simp only [d142748, d144185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d142749 q = 0) : d144186 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142749, d144186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142749, d144186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142750 q = 0) : d144187 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142750, d144187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142750, d144187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142751 q = 0) : d144188 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d142751, d144188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142751, d144188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d142755 q = 0) : d144192 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142755, d144192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12359 q selected
    | true =>
      simp only [d142755, d144192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d142756 q = 0) : d144193 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142756, d144193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142756, d144193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d142757 q = 0) : d144194 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142757, d144194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d142757, d144194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d175944 q = 0) : d177196 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d175944, d177196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16023 q selected
    | true =>
      simp only [d175944, d177196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12346 q selected
  have h9 (q : Pattern) (selected : d142783 q = 0) : d144116 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142783, d144116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12365 q selected
    | true =>
      simp only [d142783, d144116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d175945 q = 0) : d177197 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d175945, d177197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d175945, d177197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d142679 q = 0) : d144116 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142679, d144116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12346 q selected
    | true =>
      simp only [d142679, d144116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d142680 q = 0) : d144117 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142680, d144117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d142680, d144117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d175946 q = 0) : d177198 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d175946, d177198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d175946, d177198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d175947 q = 0) : d177199 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d175947, d177199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d175947, d177199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d175948 q = 0) : d177200 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d175948, d177200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d175948, d177200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d142790 q = 0) : d144214 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142790, d144214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12367 q selected
    | true =>
      simp only [d142790, d144214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d142791 q = 0) : d144215 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142791, d144215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142791, d144215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d142792 q = 0) : d144216 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142792, d144216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d142792, d144216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d142793 q = 0) : d144217 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d142793, d144217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142793, d144217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d142795 q = 0) : d144219 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142795, d144219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12368 q selected
    | true =>
      simp only [d142795, d144219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d142796 q = 0) : d144220 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142796, d144220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142796, d144220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d142797 q = 0) : d144221 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142797, d144221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d142797, d144221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d175951 q = 0) : d177203 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d175951, d177203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16025 q selected
    | true =>
      simp only [d175951, d177203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12348 q selected
  have h24 (q : Pattern) (selected : d142801 q = 0) : d144123 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142801, d144123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12370 q selected
    | true =>
      simp only [d142801, d144123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d175952 q = 0) : d177204 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d175952, d177204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d175952, d177204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d142686 q = 0) : d144123 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142686, d144123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12348 q selected
    | true =>
      simp only [d142686, d144123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d142687 q = 0) : d144124 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142687, d144124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d142687, d144124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d175953 q = 0) : d177205 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d175953, d177205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d175953, d177205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d175954 q = 0) : d177206 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d175954, d177206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d175954, d177206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d175955 q = 0) : d177207 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d175955, d177207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d175955, d177207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d175956 q = 0) : d177208 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d175956, d177208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d175956, d177208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro16027 (p : Pattern) (selected : d175963 p = 0) : d177215 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d175951 q = 0) : d177203 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d175951, d177203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16025 q selected
    | true =>
      simp only [d175951, d177203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12348 q selected
  have h2 (q : Pattern) (selected : d142801 q = 0) : d144123 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142801, d144123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12370 q selected
    | true =>
      simp only [d142801, d144123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d175952 q = 0) : d177204 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d175952, d177204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d175952, d177204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d142686 q = 0) : d144123 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142686, d144123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12348 q selected
    | true =>
      simp only [d142686, d144123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d142687 q = 0) : d144124 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142687, d144124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d142687, d144124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d175953 q = 0) : d177205 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d175953, d177205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d175953, d177205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d175961 q = 0) : d177213 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d175961, d177213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d175961, d177213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d175962 q = 0) : d177214 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d175962, d177214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d175962, d177214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d175963 q = 0) : d177215 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d175963, d177215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d175963, d177215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro16028 (p : Pattern) (selected : d12602 p = 0) : d113010 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d12599 q = 0) : d113007 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d113007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12599, d113007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6607 q selected
  have h2 (q : Pattern) (selected : d9382 q = 0) : d101015 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6607 q selected
    | true =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d12600 q = 0) : d113008 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, d113008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d12600, d113008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9384 q = 0) : d101017 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d101017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9384, d101017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d12601 q = 0) : d113009 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12601, d113009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12601, d113009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d12602 q = 0) : d113010 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12602, d113010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12602, d113010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16029 (p : Pattern) (selected : d175974 p = 0) : d177226 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d175969 q = 0) : d177221 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d175969, d177221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16028 q selected
    | true =>
      simp only [d175969, d177221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12351 q selected
  have h2 (q : Pattern) (selected : d175970 q = 0) : d177222 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d175970, d177222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d175970, d177222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d175971 q = 0) : d177223 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d175971, d177223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d175971, d177223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d142702 q = 0) : d144139 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d142702, d144139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12351 q selected
    | true =>
      simp only [d142702, d144139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d142703 q = 0) : d144140 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d142703, d144140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142703, d144140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142704 q = 0) : d144141 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d142704, d144141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142704, d144141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d175972 q = 0) : d177224 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d175972, d177224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d175972, d177224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d142705 q = 0) : d144142 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d142705, d144142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d142705, d144142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d175973 q = 0) : d177225 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d175973, d177225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d175973, d177225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d175974 q = 0) : d177226 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d175974, d177226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d175974, d177226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16030 (p : Pattern) (selected : d175980 p = 0) : d177232 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d175975 q = 0) : d177227 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d175975, d177227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16029 q selected
    | true =>
      simp only [d175975, d177227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d175976 q = 0) : d177228 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d175976, d177228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d175976, d177228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142708 q = 0) : d144145 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142708, d144145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12352 q selected
    | true =>
      simp only [d142708, d144145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142709 q = 0) : d144146 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142709, d144146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142709, d144146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d175977 q = 0) : d177229 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d175977, d177229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d175977, d177229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d175978 q = 0) : d177230 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d175978, d177230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d175978, d177230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d175979 q = 0) : d177231 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d175979, d177231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d175979, d177231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d175980 q = 0) : d177232 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d175980, d177232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d175980, d177232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16031 (p : Pattern) (selected : d175986 p = 0) : d177238 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d175981 q = 0) : d177233 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d175981, d177233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16030 q selected
    | true =>
      simp only [d175981, d177233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12353 q selected
  have h2 (q : Pattern) (selected : d142846 q = 0) : d144151 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142846, d144151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12379 q selected
    | true =>
      simp only [d142846, d144151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d175982 q = 0) : d177234 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d175982, d177234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d175982, d177234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d142714 q = 0) : d144151 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142714, d144151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12353 q selected
    | true =>
      simp only [d142714, d144151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d142715 q = 0) : d144152 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142715, d144152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d142715, d144152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d175983 q = 0) : d177235 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d175983, d177235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d175983, d177235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d175984 q = 0) : d177236 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d175984, d177236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d175984, d177236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d175985 q = 0) : d177237 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d175985, d177237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d175985, d177237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d175986 q = 0) : d177238 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d175986, d177238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d175986, d177238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro16032 (p : Pattern) (selected : d175992 p = 0) : d177244 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142736 q = 0) : d144173 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d142736, d144173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142736, d144173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12356 q selected
  have h2 (q : Pattern) (selected : d142737 q = 0) : d144174 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d142737, d144174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d142737, d144174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d142743 q = 0) : d144180 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d142743, d144180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12356 q selected
    | true =>
      simp only [d142743, d144180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12357 q selected
  have h4 (q : Pattern) (selected : d142744 q = 0) : d144181 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d142744, d144181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d142744, d144181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d142745 q = 0) : d144182 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d142745, d144182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d142745, d144182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d175957 q = 0) : d177209 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d175957, d177209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16024 q selected
    | true =>
      simp only [d175957, d177209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16026 q selected
  have h7 (q : Pattern) (selected : d142809 q = 0) : d144231 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d142809, d144231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12372 q selected
    | true =>
      simp only [d142809, d144231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d175958 q = 0) : d177210 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d175958, d177210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d175958, d177210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d175959 q = 0) : d177211 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d175959, d177211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d175959, d177211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d175960 q = 0) : d177212 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d175960, d177212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d175960, d177212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d175964 q = 0) : d177216 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d175964, d177216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d175964, d177216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16027 q selected
  have h12 (q : Pattern) (selected : d175965 q = 0) : d177217 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d175965, d177217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d175965, d177217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d175966 q = 0) : d177218 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d175966, d177218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d175966, d177218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d175967 q = 0) : d177219 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d175967, d177219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d175967, d177219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d175968 q = 0) : d177220 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d175968, d177220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d175968, d177220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d175987 q = 0) : d177239 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d175987, d177239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d175987, d177239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16031 q selected
  have h17 (q : Pattern) (selected : d175988 q = 0) : d177240 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d175988, d177240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d175988, d177240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d175989 q = 0) : d177241 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d175989, d177241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d175989, d177241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d175990 q = 0) : d177242 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d175990, d177242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d175990, d177242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d175991 q = 0) : d177243 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d175991, d177243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d175991, d177243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d175992 q = 0) : d177244 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d175992, d177244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d175992, d177244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro16033 (p : Pattern) (selected : d175998 p = 0) : d177250 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d142726 q = 0) : d144163 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d142726, d144163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142726, d144163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12355 q selected
  have h2 (q : Pattern) (selected : d142727 q = 0) : d144164 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d142727, d144164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142727, d144164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142728 q = 0) : d144165 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d142728, d144165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142728, d144165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d142729 q = 0) : d144166 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d142729, d144166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142729, d144166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d142730 q = 0) : d144167 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d142730, d144167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142730, d144167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d175993 q = 0) : d177245 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d175993, d177245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d175993, d177245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16032 q selected
  have h7 (q : Pattern) (selected : d175994 q = 0) : d177246 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d175994, d177246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d175994, d177246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d175995 q = 0) : d177247 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d175995, d177247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d175995, d177247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d175996 q = 0) : d177248 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d175996, d177248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d175996, d177248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d175997 q = 0) : d177249 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d175997, d177249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d175997, d177249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d175998 q = 0) : d177250 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d175998, d177250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d175998, d177250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16034 (p : Pattern) (selected : d176003 p = 0) : d177255 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d175944 q = 0) : d177196 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d175944, d177196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16023 q selected
    | true =>
      simp only [d175944, d177196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12346 q selected
  have h2 (q : Pattern) (selected : d175999 q = 0) : d177251 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d175999, d177251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d175999, d177251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176000 q = 0) : d177252 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176000, d177252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176000, d177252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176001 q = 0) : d177253 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176001, d177253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176001, d177253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176002 q = 0) : d177254 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176002, d177254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176002, d177254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176003 q = 0) : d177255 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176003, d177255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176003, d177255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16035 (p : Pattern) (selected : d176010 p = 0) : d177262 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d175944 q = 0) : d177196 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d175944, d177196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16023 q selected
    | true =>
      simp only [d175944, d177196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12346 q selected
  have h2 (q : Pattern) (selected : d175999 q = 0) : d177251 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d175999, d177251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d175999, d177251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176000 q = 0) : d177252 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176000, d177252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176000, d177252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176001 q = 0) : d177253 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176001, d177253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176001, d177253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176002 q = 0) : d177254 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176002, d177254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176002, d177254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d175951 q = 0) : d177203 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d175951, d177203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16025 q selected
    | true =>
      simp only [d175951, d177203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12348 q selected
  have h7 (q : Pattern) (selected : d176006 q = 0) : d177258 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176006, d177258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176006, d177258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176007 q = 0) : d177259 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176007, d177259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176007, d177259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d176008 q = 0) : d177260 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176008, d177260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176008, d177260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176009 q = 0) : d177261 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176009, d177261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176009, d177261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d176010 q = 0) : d177262 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176010, d177262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176010, d177262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16036 (p : Pattern) (selected : d176015 p = 0) : d177267 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d175938 q = 0) : d177190 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d175938, d177190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16022 q selected
    | true =>
      simp only [d175938, d177190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d175939 q = 0) : d177191 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d175939, d177191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d175939, d177191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142673 q = 0) : d144110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142673, d144110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12345 q selected
    | true =>
      simp only [d142673, d144110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142674 q = 0) : d144111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142674, d144111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142674, d144111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d175940 q = 0) : d177192 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d175940, d177192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d175940, d177192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d175941 q = 0) : d177193 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d175941, d177193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d175941, d177193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176014 q = 0) : d177266 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176014, d177266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176014, d177266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176015 q = 0) : d177267 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176015, d177267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176015, d177267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16037 (p : Pattern) (selected : d176022 p = 0) : d177274 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d175938 q = 0) : d177190 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d175938, d177190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16022 q selected
    | true =>
      simp only [d175938, d177190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d175939 q = 0) : d177191 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d175939, d177191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d175939, d177191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142673 q = 0) : d144110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142673, d144110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12345 q selected
    | true =>
      simp only [d142673, d144110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142674 q = 0) : d144111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142674, d144111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142674, d144111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d175940 q = 0) : d177192 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d175940, d177192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d175940, d177192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176020 q = 0) : d177272 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176020, d177272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176020, d177272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176021 q = 0) : d177273 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176021, d177273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176021, d177273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176022 q = 0) : d177274 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176022, d177274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176022, d177274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16038 (p : Pattern) (selected : d12749 p = 0) : d113135 p = 1 := by
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
  have h3 (q : Pattern) (selected : d12748 q = 0) : d113134 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12748, d113134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12748, d113134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d12749 q = 0) : d113135 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12749, d113135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12749, d113135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16039 (p : Pattern) (selected : d176031 p = 0) : d177283 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176026 q = 0) : d177278 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176026, d177278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16038 q selected
    | true =>
      simp only [d176026, d177278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16021 q selected
  have h2 (q : Pattern) (selected : d176027 q = 0) : d177279 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176027, d177279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176027, d177279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176028 q = 0) : d177280 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176028, d177280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176028, d177280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d175932 q = 0) : d177184 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d175932, d177184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16021 q selected
    | true =>
      simp only [d175932, d177184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12344 q selected
  have h5 (q : Pattern) (selected : d175933 q = 0) : d177185 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d175933, d177185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d175933, d177185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d175934 q = 0) : d177186 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d175934, d177186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d175934, d177186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176029 q = 0) : d177281 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176029, d177281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176029, d177281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d142667 q = 0) : d144104 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d142667, d144104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12344 q selected
    | true =>
      simp only [d142667, d144104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d142668 q = 0) : d144105 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d142668, d144105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142668, d144105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d142669 q = 0) : d144106 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d142669, d144106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142669, d144106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d175935 q = 0) : d177187 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d175935, d177187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d175935, d177187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d176030 q = 0) : d177282 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176030, d177282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176030, d177282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d176031 q = 0) : d177283 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176031, d177283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d176031, d177283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro16040 (p : Pattern) (selected : d176037 p = 0) : d177289 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176032 q = 0) : d177284 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176032, d177284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16039 q selected
    | true =>
      simp only [d176032, d177284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176033 q = 0) : d177285 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176033, d177285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176033, d177285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d175938 q = 0) : d177190 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d175938, d177190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16022 q selected
    | true =>
      simp only [d175938, d177190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d175939 q = 0) : d177191 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d175939, d177191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d175939, d177191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176034 q = 0) : d177286 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176034, d177286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176034, d177286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176035 q = 0) : d177287 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176035, d177287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176035, d177287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176036 q = 0) : d177288 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176036, d177288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176036, d177288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176037 q = 0) : d177289 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176037, d177289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176037, d177289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16041 (p : Pattern) (selected : d14283 p = 0) : d112928 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d9512 q = 0) : d101015 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9512, d101015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6628 q selected
    | true =>
      simp only [d9512, d101015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9514 q = 0) : d101017 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9514, d101017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9514, d101017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d14282 q = 0) : d112927 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14282, d112927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14282, d112927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d14283 q = 0) : d112928 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14283, d112928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14283, d112928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16042 (p : Pattern) (selected : d176044 p = 0) : d177189 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176039 q = 0) : d177184 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176039, d177184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16041 q selected
    | true =>
      simp only [d176039, d177184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12363 q selected
  have h2 (q : Pattern) (selected : d176040 q = 0) : d177185 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176040, d177185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176040, d177185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176041 q = 0) : d177186 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176041, d177186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176041, d177186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d142771 q = 0) : d144104 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d142771, d144104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12363 q selected
    | true =>
      simp only [d142771, d144104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d142772 q = 0) : d144105 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d142772, d144105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142772, d144105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142773 q = 0) : d144106 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d142773, d144106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142773, d144106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176042 q = 0) : d177187 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176042, d177187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176042, d177187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d142774 q = 0) : d144107 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d142774, d144107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d142774, d144107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d176043 q = 0) : d177188 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176043, d177188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176043, d177188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176044 q = 0) : d177189 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176044, d177189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d176044, d177189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16043 (p : Pattern) (selected : d176050 p = 0) : d177195 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176045 q = 0) : d177190 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176045, d177190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16042 q selected
    | true =>
      simp only [d176045, d177190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176046 q = 0) : d177191 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176046, d177191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176046, d177191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142777 q = 0) : d144110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142777, d144110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12364 q selected
    | true =>
      simp only [d142777, d144110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142778 q = 0) : d144111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142778, d144111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142778, d144111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176047 q = 0) : d177192 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176047, d177192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176047, d177192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176048 q = 0) : d177193 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176048, d177193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176048, d177193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176049 q = 0) : d177194 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176049, d177194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176049, d177194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176050 q = 0) : d177195 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176050, d177195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176050, d177195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16044 (p : Pattern) (selected : d176056 p = 0) : d177295 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d175938 q = 0) : d177190 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d175938, d177190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16022 q selected
    | true =>
      simp only [d175938, d177190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d175939 q = 0) : d177191 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d175939, d177191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d175939, d177191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176053 q = 0) : d177292 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176053, d177292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176053, d177292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176054 q = 0) : d177293 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176054, d177293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176054, d177293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176055 q = 0) : d177294 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176055, d177294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176055, d177294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176056 q = 0) : d177295 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176056, d177295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176056, d177295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16045 (p : Pattern) (selected : d176062 p = 0) : d177301 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176016 q = 0) : d177268 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176016, d177268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16036 q selected
    | true =>
      simp only [d176016, d177268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12358 q selected
  have h2 (q : Pattern) (selected : d176017 q = 0) : d177269 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176017, d177269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176017, d177269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176018 q = 0) : d177270 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176018, d177270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176018, d177270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176019 q = 0) : d177271 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176019, d177271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176019, d177271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176023 q = 0) : d177275 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176023, d177275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16037 q selected
    | true =>
      simp only [d176023, d177275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12359 q selected
  have h6 (q : Pattern) (selected : d176024 q = 0) : d177276 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176024, d177276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176024, d177276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176025 q = 0) : d177277 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176025, d177277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176025, d177277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176038 q = 0) : d177290 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176038, d177290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16040 q selected
    | true =>
      simp only [d176038, d177290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16023 q selected
  have h9 (q : Pattern) (selected : d176051 q = 0) : d177196 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176051, d177196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16043 q selected
    | true =>
      simp only [d176051, d177196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12365 q selected
  have h10 (q : Pattern) (selected : d176052 q = 0) : d177291 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176052, d177291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d176052, d177291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d176057 q = 0) : d177296 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176057, d177296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16044 q selected
    | true =>
      simp only [d176057, d177296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d176058 q = 0) : d177297 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176058, d177297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d176058, d177297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d176059 q = 0) : d177298 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176059, d177298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d176059, d177298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d176060 q = 0) : d177299 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176060, d177299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176060, d177299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d176061 q = 0) : d177300 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176061, d177300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176061, d177300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d176062 q = 0) : d177301 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176062, d177301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176062, d177301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro16046 (p : Pattern) (selected : d176063 p = 0) : d177302 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d175938 q = 0) : d177190 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d175938, d177190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16022 q selected
    | true =>
      simp only [d175938, d177190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d175939 q = 0) : d177191 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d175939, d177191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d175939, d177191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142673 q = 0) : d144110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142673, d144110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12345 q selected
    | true =>
      simp only [d142673, d144110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142674 q = 0) : d144111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142674, d144111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142674, d144111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d175940 q = 0) : d177192 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d175940, d177192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d175940, d177192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d175941 q = 0) : d177193 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d175941, d177193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d175941, d177193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176014 q = 0) : d177266 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176014, d177266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176014, d177266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176063 q = 0) : d177302 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176063, d177302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176063, d177302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16047 (p : Pattern) (selected : d176068 p = 0) : d177307 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d175938 q = 0) : d177190 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d175938, d177190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16022 q selected
    | true =>
      simp only [d175938, d177190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d175939 q = 0) : d177191 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d175939, d177191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d175939, d177191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142673 q = 0) : d144110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142673, d144110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12345 q selected
    | true =>
      simp only [d142673, d144110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142674 q = 0) : d144111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142674, d144111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142674, d144111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d175940 q = 0) : d177192 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d175940, d177192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d175940, d177192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176020 q = 0) : d177272 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176020, d177272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176020, d177272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176021 q = 0) : d177273 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176021, d177273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176021, d177273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176068 q = 0) : d177307 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176068, d177307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176068, d177307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16048 (p : Pattern) (selected : d176072 p = 0) : d177311 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176032 q = 0) : d177284 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176032, d177284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16039 q selected
    | true =>
      simp only [d176032, d177284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176033 q = 0) : d177285 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176033, d177285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176033, d177285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d175938 q = 0) : d177190 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d175938, d177190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16022 q selected
    | true =>
      simp only [d175938, d177190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d175939 q = 0) : d177191 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d175939, d177191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d175939, d177191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176034 q = 0) : d177286 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176034, d177286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176034, d177286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176035 q = 0) : d177287 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176035, d177287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176035, d177287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176036 q = 0) : d177288 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176036, d177288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176036, d177288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176072 q = 0) : d177311 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176072, d177311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176072, d177311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16049 (p : Pattern) (selected : d176074 p = 0) : d177202 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176045 q = 0) : d177190 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176045, d177190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16042 q selected
    | true =>
      simp only [d176045, d177190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176046 q = 0) : d177191 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176046, d177191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176046, d177191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142777 q = 0) : d144110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142777, d144110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12364 q selected
    | true =>
      simp only [d142777, d144110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142778 q = 0) : d144111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142778, d144111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142778, d144111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176047 q = 0) : d177192 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176047, d177192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176047, d177192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176048 q = 0) : d177193 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176048, d177193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176048, d177193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176049 q = 0) : d177194 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176049, d177194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176049, d177194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176074 q = 0) : d177202 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176074, d177202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176074, d177202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16050 (p : Pattern) (selected : d176077 p = 0) : d177314 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d175938 q = 0) : d177190 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d175938, d177190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16022 q selected
    | true =>
      simp only [d175938, d177190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d175939 q = 0) : d177191 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d175939, d177191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d175939, d177191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176053 q = 0) : d177292 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176053, d177292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176053, d177292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176054 q = 0) : d177293 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176054, d177293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176054, d177293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176055 q = 0) : d177294 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176055, d177294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176055, d177294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176077 q = 0) : d177314 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176077, d177314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176077, d177314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16051 (p : Pattern) (selected : d176083 p = 0) : d177320 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176016 q = 0) : d177268 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176016, d177268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16036 q selected
    | true =>
      simp only [d176016, d177268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12358 q selected
  have h2 (q : Pattern) (selected : d176017 q = 0) : d177269 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176017, d177269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176017, d177269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176018 q = 0) : d177270 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176018, d177270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176018, d177270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176019 q = 0) : d177271 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176019, d177271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176019, d177271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176023 q = 0) : d177275 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176023, d177275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16037 q selected
    | true =>
      simp only [d176023, d177275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12359 q selected
  have h6 (q : Pattern) (selected : d176024 q = 0) : d177276 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176024, d177276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176024, d177276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176025 q = 0) : d177277 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176025, d177277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176025, d177277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176038 q = 0) : d177290 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176038, d177290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16040 q selected
    | true =>
      simp only [d176038, d177290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16023 q selected
  have h9 (q : Pattern) (selected : d176051 q = 0) : d177196 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176051, d177196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16043 q selected
    | true =>
      simp only [d176051, d177196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12365 q selected
  have h10 (q : Pattern) (selected : d176052 q = 0) : d177291 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176052, d177291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d176052, d177291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d176057 q = 0) : d177296 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176057, d177296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16044 q selected
    | true =>
      simp only [d176057, d177296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d176058 q = 0) : d177297 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176058, d177297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d176058, d177297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d176059 q = 0) : d177298 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176059, d177298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d176059, d177298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d176060 q = 0) : d177299 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176060, d177299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176060, d177299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d176061 q = 0) : d177300 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176061, d177300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176061, d177300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d176064 q = 0) : d177303 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176064, d177303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16046 q selected
    | true =>
      simp only [d176064, d177303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12367 q selected
  have h17 (q : Pattern) (selected : d176065 q = 0) : d177304 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176065, d177304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176065, d177304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d176066 q = 0) : d177305 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176066, d177305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d176066, d177305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d176067 q = 0) : d177306 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176067, d177306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176067, d177306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d176069 q = 0) : d177308 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176069, d177308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16047 q selected
    | true =>
      simp only [d176069, d177308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12368 q selected
  have h21 (q : Pattern) (selected : d176070 q = 0) : d177309 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176070, d177309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176070, d177309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d176071 q = 0) : d177310 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176071, d177310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d176071, d177310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d176073 q = 0) : d177312 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176073, d177312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16048 q selected
    | true =>
      simp only [d176073, d177312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16025 q selected
  have h24 (q : Pattern) (selected : d176075 q = 0) : d177203 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176075, d177203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16049 q selected
    | true =>
      simp only [d176075, d177203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12370 q selected
  have h25 (q : Pattern) (selected : d176076 q = 0) : d177313 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176076, d177313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d176076, d177313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d176078 q = 0) : d177315 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176078, d177315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16050 q selected
    | true =>
      simp only [d176078, d177315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d176079 q = 0) : d177316 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176079, d177316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d176079, d177316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d176080 q = 0) : d177317 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176080, d177317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d176080, d177317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d176081 q = 0) : d177318 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176081, d177318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d176081, d177318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d176082 q = 0) : d177319 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176082, d177319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d176082, d177319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d176083 q = 0) : d177320 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176083, d177320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d176083, d177320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro16052 (p : Pattern) (selected : d176085 p = 0) : d177322 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d175944 q = 0) : d177196 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d175944, d177196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16023 q selected
    | true =>
      simp only [d175944, d177196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12346 q selected
  have h2 (q : Pattern) (selected : d175999 q = 0) : d177251 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d175999, d177251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d175999, d177251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176000 q = 0) : d177252 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176000, d177252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176000, d177252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176001 q = 0) : d177253 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176001, d177253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176001, d177253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176002 q = 0) : d177254 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176002, d177254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176002, d177254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142679 q = 0) : d144116 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142679, d144116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12346 q selected
    | true =>
      simp only [d142679, d144116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d142731 q = 0) : d144168 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d142731, d144168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142731, d144168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d142732 q = 0) : d144169 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d142732, d144169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d142732, d144169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d142733 q = 0) : d144170 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d142733, d144170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142733, d144170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d142734 q = 0) : d144171 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d142734, d144171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142734, d144171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d176085 q = 0) : d177322 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176085, d177322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176085, d177322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16053 (p : Pattern) (selected : d176092 p = 0) : d177329 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176073 q = 0) : d177312 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176073, d177312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16048 q selected
    | true =>
      simp only [d176073, d177312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16025 q selected
  have h2 (q : Pattern) (selected : d176075 q = 0) : d177203 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176075, d177203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16049 q selected
    | true =>
      simp only [d176075, d177203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12370 q selected
  have h3 (q : Pattern) (selected : d176076 q = 0) : d177313 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176076, d177313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d176076, d177313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176078 q = 0) : d177315 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176078, d177315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16050 q selected
    | true =>
      simp only [d176078, d177315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176079 q = 0) : d177316 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176079, d177316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176079, d177316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176080 q = 0) : d177317 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176080, d177317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176080, d177317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176090 q = 0) : d177327 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176090, d177327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176090, d177327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176091 q = 0) : d177328 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176091, d177328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176091, d177328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d176092 q = 0) : d177329 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176092, d177329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176092, d177329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro16054 (p : Pattern) (selected : d12861 p = 0) : d113217 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d12858 q = 0) : d113214 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, d113214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12858, d113214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6620 q selected
  have h2 (q : Pattern) (selected : d9468 q = 0) : d101083 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6620 q selected
    | true =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d12859 q = 0) : d113215 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12859, d113215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d12859, d113215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9470 q = 0) : d101085 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d12860 q = 0) : d113216 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12860, d113216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12860, d113216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d12861 q = 0) : d113217 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12861, d113217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12861, d113217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16055 (p : Pattern) (selected : d176103 p = 0) : d177340 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176098 q = 0) : d177335 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176098, d177335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16054 q selected
    | true =>
      simp only [d176098, d177335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16028 q selected
  have h2 (q : Pattern) (selected : d176099 q = 0) : d177336 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176099, d177336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176099, d177336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176100 q = 0) : d177337 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176100, d177337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176100, d177337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d175969 q = 0) : d177221 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d175969, d177221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16028 q selected
    | true =>
      simp only [d175969, d177221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12351 q selected
  have h5 (q : Pattern) (selected : d175970 q = 0) : d177222 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d175970, d177222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d175970, d177222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d175971 q = 0) : d177223 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d175971, d177223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d175971, d177223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176101 q = 0) : d177338 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176101, d177338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176101, d177338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d142702 q = 0) : d144139 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d142702, d144139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12351 q selected
    | true =>
      simp only [d142702, d144139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d142703 q = 0) : d144140 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d142703, d144140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142703, d144140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d142704 q = 0) : d144141 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d142704, d144141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142704, d144141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d175972 q = 0) : d177224 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d175972, d177224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d175972, d177224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d176102 q = 0) : d177339 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176102, d177339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176102, d177339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d176103 q = 0) : d177340 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176103, d177340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d176103, d177340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro16056 (p : Pattern) (selected : d176109 p = 0) : d177346 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176104 q = 0) : d177341 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176104, d177341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16055 q selected
    | true =>
      simp only [d176104, d177341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176105 q = 0) : d177342 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176105, d177342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176105, d177342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d175975 q = 0) : d177227 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d175975, d177227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16029 q selected
    | true =>
      simp only [d175975, d177227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d175976 q = 0) : d177228 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d175976, d177228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d175976, d177228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176106 q = 0) : d177343 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176106, d177343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176106, d177343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176107 q = 0) : d177344 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176107, d177344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176107, d177344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176108 q = 0) : d177345 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176108, d177345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176108, d177345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176109 q = 0) : d177346 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176109, d177346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176109, d177346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16057 (p : Pattern) (selected : d14407 p = 0) : d113010 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14404 q = 0) : d113007 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14404, d113007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14404, d113007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6628 q selected
  have h2 (q : Pattern) (selected : d9512 q = 0) : d101015 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9512, d101015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6628 q selected
    | true =>
      simp only [d9512, d101015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d14405 q = 0) : d113008 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14405, d113008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d14405, d113008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9514 q = 0) : d101017 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9514, d101017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9514, d101017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14406 q = 0) : d113009 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14406, d113009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14406, d113009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14407 q = 0) : d113010 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14407, d113010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14407, d113010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16058 (p : Pattern) (selected : d176116 p = 0) : d177226 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176111 q = 0) : d177221 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176111, d177221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16057 q selected
    | true =>
      simp only [d176111, d177221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12377 q selected
  have h2 (q : Pattern) (selected : d176112 q = 0) : d177222 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176112, d177222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176112, d177222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176113 q = 0) : d177223 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176113, d177223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176113, d177223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d142834 q = 0) : d144139 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d142834, d144139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12377 q selected
    | true =>
      simp only [d142834, d144139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d142835 q = 0) : d144140 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d142835, d144140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142835, d144140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142836 q = 0) : d144141 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d142836, d144141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142836, d144141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176114 q = 0) : d177224 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176114, d177224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176114, d177224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d142837 q = 0) : d144142 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d142837, d144142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d142837, d144142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d176115 q = 0) : d177225 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176115, d177225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176115, d177225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176116 q = 0) : d177226 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176116, d177226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d176116, d177226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16059 (p : Pattern) (selected : d176122 p = 0) : d177232 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176117 q = 0) : d177227 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176117, d177227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16058 q selected
    | true =>
      simp only [d176117, d177227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176118 q = 0) : d177228 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176118, d177228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176118, d177228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142840 q = 0) : d144145 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142840, d144145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12378 q selected
    | true =>
      simp only [d142840, d144145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142841 q = 0) : d144146 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142841, d144146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142841, d144146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176119 q = 0) : d177229 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176119, d177229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176119, d177229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176120 q = 0) : d177230 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176120, d177230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176120, d177230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176121 q = 0) : d177231 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176121, d177231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176121, d177231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176122 q = 0) : d177232 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176122, d177232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176122, d177232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16060 (p : Pattern) (selected : d176128 p = 0) : d177352 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d175975 q = 0) : d177227 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d175975, d177227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16029 q selected
    | true =>
      simp only [d175975, d177227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d175976 q = 0) : d177228 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d175976, d177228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d175976, d177228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176125 q = 0) : d177349 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176125, d177349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176125, d177349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176126 q = 0) : d177350 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176126, d177350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176126, d177350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176127 q = 0) : d177351 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176127, d177351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176127, d177351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176128 q = 0) : d177352 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176128, d177352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176128, d177352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16061 (p : Pattern) (selected : d176134 p = 0) : d177358 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176110 q = 0) : d177347 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176110, d177347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16056 q selected
    | true =>
      simp only [d176110, d177347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16030 q selected
  have h2 (q : Pattern) (selected : d176123 q = 0) : d177233 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176123, d177233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16059 q selected
    | true =>
      simp only [d176123, d177233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12379 q selected
  have h3 (q : Pattern) (selected : d176124 q = 0) : d177348 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176124, d177348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d176124, d177348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176129 q = 0) : d177353 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176129, d177353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16060 q selected
    | true =>
      simp only [d176129, d177353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176130 q = 0) : d177354 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176130, d177354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176130, d177354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176131 q = 0) : d177355 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176131, d177355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176131, d177355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176132 q = 0) : d177356 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176132, d177356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176132, d177356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176133 q = 0) : d177357 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176133, d177357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176133, d177357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d176134 q = 0) : d177358 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176134, d177358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176134, d177358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro16062 (p : Pattern) (selected : d176140 p = 0) : d177364 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176004 q = 0) : d177256 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d176004, d177256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176004, d177256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16034 q selected
  have h2 (q : Pattern) (selected : d176005 q = 0) : d177257 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d176005, d177257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d176005, d177257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d176011 q = 0) : d177263 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d176011, d177263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16034 q selected
    | true =>
      simp only [d176011, d177263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16035 q selected
  have h4 (q : Pattern) (selected : d176012 q = 0) : d177264 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d176012, d177264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176012, d177264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176013 q = 0) : d177265 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d176013, d177265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176013, d177265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176084 q = 0) : d177321 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d176084, d177321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16045 q selected
    | true =>
      simp only [d176084, d177321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16051 q selected
  have h7 (q : Pattern) (selected : d176086 q = 0) : d177323 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d176086, d177323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16052 q selected
    | true =>
      simp only [d176086, d177323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12357 q selected
  have h8 (q : Pattern) (selected : d176087 q = 0) : d177324 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d176087, d177324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176087, d177324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d176088 q = 0) : d177325 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d176088, d177325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d176088, d177325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d176089 q = 0) : d177326 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d176089, d177326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176089, d177326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d176093 q = 0) : d177330 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d176093, d177330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176093, d177330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16053 q selected
  have h12 (q : Pattern) (selected : d142960 q = 0) : d144354 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d142960, d144354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142960, d144354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12403 q selected
  have h13 (q : Pattern) (selected : d176094 q = 0) : d177331 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d176094, d177331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d176094, d177331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d176095 q = 0) : d177332 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d176095, d177332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d176095, d177332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d176096 q = 0) : d177333 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d176096, d177333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d176096, d177333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d176097 q = 0) : d177334 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d176097, d177334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d176097, d177334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d176135 q = 0) : d177359 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d176135, d177359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176135, d177359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16061 q selected
  have h18 (q : Pattern) (selected : d143008 q = 0) : d144389 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d143008, d144389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143008, d144389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12412 q selected
  have h19 (q : Pattern) (selected : d176136 q = 0) : d177360 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d176136, d177360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d176136, d177360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d176137 q = 0) : d177361 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d176137, d177361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d176137, d177361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d176138 q = 0) : d177362 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d176138, d177362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d176138, d177362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d176139 q = 0) : d177363 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d176139, d177363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d176139, d177363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d176140 q = 0) : d177364 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d176140, d177364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d176140, d177364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro16063 (p : Pattern) (selected : d176146 p = 0) : d177370 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176141 q = 0) : d177365 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d176141, d177365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176141, d177365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16062 q selected
  have h2 (q : Pattern) (selected : d176142 q = 0) : d177366 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d176142, d177366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176142, d177366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176143 q = 0) : d177367 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d176143, d177367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176143, d177367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176144 q = 0) : d177368 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d176144, d177368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176144, d177368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176145 q = 0) : d177369 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d176145, d177369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176145, d177369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176146 q = 0) : d177370 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d176146, d177370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176146, d177370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16064 (p : Pattern) (selected : d176153 p = 0) : d177377 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176148 q = 0) : d177372 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176148, d177372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16038 q selected
    | true =>
      simp only [d176148, d177372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12415 q selected
  have h2 (q : Pattern) (selected : d176149 q = 0) : d177373 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176149, d177373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176149, d177373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176150 q = 0) : d177374 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176150, d177374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176150, d177374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143024 q = 0) : d144405 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143024, d144405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12415 q selected
    | true =>
      simp only [d143024, d144405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143025 q = 0) : d144406 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143025, d144406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143025, d144406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143026 q = 0) : d144407 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143026, d144407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143026, d144407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176151 q = 0) : d177375 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176151, d177375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176151, d177375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143028 q = 0) : d144409 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143028, d144409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143028, d144409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d176152 q = 0) : d177376 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176152, d177376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176152, d177376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176153 q = 0) : d177377 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176153, d177377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d176153, d177377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16065 (p : Pattern) (selected : d176159 p = 0) : d177383 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176154 q = 0) : d177378 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176154, d177378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16064 q selected
    | true =>
      simp only [d176154, d177378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176155 q = 0) : d177379 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176155, d177379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176155, d177379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143035 q = 0) : d144416 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143035, d144416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12417 q selected
    | true =>
      simp only [d143035, d144416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143036 q = 0) : d144417 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143036, d144417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143036, d144417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176156 q = 0) : d177380 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176156, d177380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176156, d177380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176157 q = 0) : d177381 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176157, d177381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176157, d177381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176158 q = 0) : d177382 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176158, d177382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176158, d177382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176159 q = 0) : d177383 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176159, d177383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176159, d177383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16066 (p : Pattern) (selected : d176165 p = 0) : d177389 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176160 q = 0) : d177384 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176160, d177384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16065 q selected
    | true =>
      simp only [d176160, d177384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12419 q selected
  have h2 (q : Pattern) (selected : d176161 q = 0) : d177385 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176161, d177385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176161, d177385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176162 q = 0) : d177386 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176162, d177386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176162, d177386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176163 q = 0) : d177387 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176163, d177387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176163, d177387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176164 q = 0) : d177388 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176164, d177388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176164, d177388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176165 q = 0) : d177389 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176165, d177389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176165, d177389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16067 (p : Pattern) (selected : d176168 p = 0) : d177392 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176154 q = 0) : d177378 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176154, d177378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16064 q selected
    | true =>
      simp only [d176154, d177378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176155 q = 0) : d177379 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176155, d177379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176155, d177379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143035 q = 0) : d144416 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143035, d144416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12417 q selected
    | true =>
      simp only [d143035, d144416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143036 q = 0) : d144417 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143036, d144417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143036, d144417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176156 q = 0) : d177380 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176156, d177380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176156, d177380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176157 q = 0) : d177381 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176157, d177381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176157, d177381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176158 q = 0) : d177382 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176158, d177382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176158, d177382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176168 q = 0) : d177392 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176168, d177392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176168, d177392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16068 (p : Pattern) (selected : d176174 p = 0) : d177398 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176160 q = 0) : d177384 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176160, d177384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16065 q selected
    | true =>
      simp only [d176160, d177384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12419 q selected
  have h2 (q : Pattern) (selected : d176161 q = 0) : d177385 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176161, d177385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176161, d177385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176162 q = 0) : d177386 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176162, d177386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176162, d177386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176163 q = 0) : d177387 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176163, d177387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176163, d177387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176164 q = 0) : d177388 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176164, d177388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176164, d177388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176169 q = 0) : d177393 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176169, d177393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16067 q selected
    | true =>
      simp only [d176169, d177393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12422 q selected
  have h7 (q : Pattern) (selected : d176170 q = 0) : d177394 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176170, d177394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176170, d177394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176171 q = 0) : d177395 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176171, d177395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176171, d177395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d176172 q = 0) : d177396 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176172, d177396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176172, d177396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176173 q = 0) : d177397 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176173, d177397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176173, d177397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d176174 q = 0) : d177398 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176174, d177398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176174, d177398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16069 (p : Pattern) (selected : d176179 p = 0) : d177403 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176154 q = 0) : d177378 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176154, d177378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16064 q selected
    | true =>
      simp only [d176154, d177378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176155 q = 0) : d177379 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176155, d177379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176155, d177379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143035 q = 0) : d144416 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143035, d144416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12417 q selected
    | true =>
      simp only [d143035, d144416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143036 q = 0) : d144417 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143036, d144417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143036, d144417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176156 q = 0) : d177380 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176156, d177380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176156, d177380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176157 q = 0) : d177381 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176157, d177381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176157, d177381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176178 q = 0) : d177402 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176178, d177402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176178, d177402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176179 q = 0) : d177403 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176179, d177403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176179, d177403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16070 (p : Pattern) (selected : d176186 p = 0) : d177410 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176154 q = 0) : d177378 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176154, d177378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16064 q selected
    | true =>
      simp only [d176154, d177378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176155 q = 0) : d177379 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176155, d177379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176155, d177379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143035 q = 0) : d144416 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143035, d144416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12417 q selected
    | true =>
      simp only [d143035, d144416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143036 q = 0) : d144417 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143036, d144417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143036, d144417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176156 q = 0) : d177380 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176156, d177380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176156, d177380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176184 q = 0) : d177408 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176184, d177408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176184, d177408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176185 q = 0) : d177409 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176185, d177409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176185, d177409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176186 q = 0) : d177410 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176186, d177410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176186, d177410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16071 (p : Pattern) (selected : d14530 p = 0) : d122767 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d9597 q = 0) : d101177 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9597, d101177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6642 q selected
    | true =>
      simp only [d9597, d101177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9599 q = 0) : d101179 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9599, d101179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9599, d101179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d14529 q = 0) : d122766 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14529, d122766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14529, d122766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d14530 q = 0) : d122767 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14530, d122767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14530, d122767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16072 (p : Pattern) (selected : d176195 p = 0) : d177419 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176190 q = 0) : d177414 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176190, d177414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16071 q selected
    | true =>
      simp only [d176190, d177414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16038 q selected
  have h2 (q : Pattern) (selected : d176191 q = 0) : d177415 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176191, d177415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176191, d177415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176192 q = 0) : d177416 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176192, d177416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176192, d177416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176148 q = 0) : d177372 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176148, d177372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16038 q selected
    | true =>
      simp only [d176148, d177372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12415 q selected
  have h5 (q : Pattern) (selected : d176149 q = 0) : d177373 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176149, d177373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176149, d177373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176150 q = 0) : d177374 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176150, d177374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176150, d177374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176193 q = 0) : d177417 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176193, d177417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176193, d177417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143024 q = 0) : d144405 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143024, d144405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12415 q selected
    | true =>
      simp only [d143024, d144405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d143025 q = 0) : d144406 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143025, d144406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143025, d144406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d143026 q = 0) : d144407 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143026, d144407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143026, d144407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d176151 q = 0) : d177375 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176151, d177375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176151, d177375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d176194 q = 0) : d177418 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176194, d177418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176194, d177418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d176195 q = 0) : d177419 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176195, d177419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d176195, d177419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro16073 (p : Pattern) (selected : d176201 p = 0) : d177425 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176196 q = 0) : d177420 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176196, d177420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16072 q selected
    | true =>
      simp only [d176196, d177420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176197 q = 0) : d177421 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176197, d177421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176197, d177421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176154 q = 0) : d177378 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176154, d177378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16064 q selected
    | true =>
      simp only [d176154, d177378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176155 q = 0) : d177379 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176155, d177379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176155, d177379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176198 q = 0) : d177422 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176198, d177422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176198, d177422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176199 q = 0) : d177423 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176199, d177423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176199, d177423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176200 q = 0) : d177424 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176200, d177424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176200, d177424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176201 q = 0) : d177425 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176201, d177425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176201, d177425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16074 (p : Pattern) (selected : d14552 p = 0) : d113135 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d9671 q = 0) : d101083 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9671, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6655 q selected
    | true =>
      simp only [d9671, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9673 q = 0) : d101085 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9673, d101085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9673, d101085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d14551 q = 0) : d113134 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14551, d113134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14551, d113134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d14552 q = 0) : d113135 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14552, d113135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14552, d113135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16075 (p : Pattern) (selected : d176208 p = 0) : d177377 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176203 q = 0) : d177372 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176203, d177372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16074 q selected
    | true =>
      simp only [d176203, d177372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12432 q selected
  have h2 (q : Pattern) (selected : d176204 q = 0) : d177373 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176204, d177373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176204, d177373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176205 q = 0) : d177374 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176205, d177374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176205, d177374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143097 q = 0) : d144405 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143097, d144405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12432 q selected
    | true =>
      simp only [d143097, d144405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143098 q = 0) : d144406 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143098, d144406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143098, d144406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143099 q = 0) : d144407 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143099, d144407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143099, d144407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176206 q = 0) : d177375 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176206, d177375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176206, d177375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143101 q = 0) : d144409 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143101, d144409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143101, d144409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d176207 q = 0) : d177376 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176207, d177376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176207, d177376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176208 q = 0) : d177377 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176208, d177377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d176208, d177377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16076 (p : Pattern) (selected : d176214 p = 0) : d177383 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176209 q = 0) : d177378 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176209, d177378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16075 q selected
    | true =>
      simp only [d176209, d177378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176210 q = 0) : d177379 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176210, d177379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176210, d177379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143108 q = 0) : d144416 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143108, d144416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12434 q selected
    | true =>
      simp only [d143108, d144416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143109 q = 0) : d144417 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143109, d144417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143109, d144417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176211 q = 0) : d177380 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176211, d177380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176211, d177380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176212 q = 0) : d177381 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176212, d177381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176212, d177381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176213 q = 0) : d177382 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176213, d177382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176213, d177382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176214 q = 0) : d177383 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176214, d177383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176214, d177383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16077 (p : Pattern) (selected : d176220 p = 0) : d177431 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176154 q = 0) : d177378 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176154, d177378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16064 q selected
    | true =>
      simp only [d176154, d177378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176155 q = 0) : d177379 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176155, d177379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176155, d177379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176217 q = 0) : d177428 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176217, d177428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176217, d177428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176218 q = 0) : d177429 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176218, d177429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176218, d177429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176219 q = 0) : d177430 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176219, d177430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176219, d177430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176220 q = 0) : d177431 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176220, d177431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176220, d177431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16078 (p : Pattern) (selected : d176226 p = 0) : d177437 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176180 q = 0) : d177404 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176180, d177404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16069 q selected
    | true =>
      simp only [d176180, d177404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12425 q selected
  have h2 (q : Pattern) (selected : d176181 q = 0) : d177405 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176181, d177405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176181, d177405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176182 q = 0) : d177406 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176182, d177406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176182, d177406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176183 q = 0) : d177407 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176183, d177407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176183, d177407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176187 q = 0) : d177411 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176187, d177411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16070 q selected
    | true =>
      simp only [d176187, d177411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12427 q selected
  have h6 (q : Pattern) (selected : d176188 q = 0) : d177412 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176188, d177412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176188, d177412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176189 q = 0) : d177413 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176189, d177413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176189, d177413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176202 q = 0) : d177426 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176202, d177426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16073 q selected
    | true =>
      simp only [d176202, d177426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16065 q selected
  have h9 (q : Pattern) (selected : d176215 q = 0) : d177384 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176215, d177384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16076 q selected
    | true =>
      simp only [d176215, d177384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12436 q selected
  have h10 (q : Pattern) (selected : d176216 q = 0) : d177427 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176216, d177427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d176216, d177427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d176221 q = 0) : d177432 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176221, d177432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16077 q selected
    | true =>
      simp only [d176221, d177432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d176222 q = 0) : d177433 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176222, d177433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d176222, d177433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d176223 q = 0) : d177434 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176223, d177434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d176223, d177434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d176224 q = 0) : d177435 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176224, d177435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176224, d177435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d176225 q = 0) : d177436 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176225, d177436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176225, d177436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d176226 q = 0) : d177437 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176226, d177437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176226, d177437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro16079 (p : Pattern) (selected : d176227 p = 0) : d177438 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176154 q = 0) : d177378 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176154, d177378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16064 q selected
    | true =>
      simp only [d176154, d177378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176155 q = 0) : d177379 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176155, d177379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176155, d177379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143035 q = 0) : d144416 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143035, d144416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12417 q selected
    | true =>
      simp only [d143035, d144416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143036 q = 0) : d144417 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143036, d144417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143036, d144417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176156 q = 0) : d177380 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176156, d177380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176156, d177380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176157 q = 0) : d177381 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176157, d177381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176157, d177381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176178 q = 0) : d177402 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176178, d177402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176178, d177402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176227 q = 0) : d177438 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176227, d177438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176227, d177438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16080 (p : Pattern) (selected : d176232 p = 0) : d177443 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176154 q = 0) : d177378 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176154, d177378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16064 q selected
    | true =>
      simp only [d176154, d177378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176155 q = 0) : d177379 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176155, d177379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176155, d177379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143035 q = 0) : d144416 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143035, d144416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12417 q selected
    | true =>
      simp only [d143035, d144416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143036 q = 0) : d144417 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143036, d144417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143036, d144417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176156 q = 0) : d177380 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176156, d177380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176156, d177380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176184 q = 0) : d177408 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176184, d177408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176184, d177408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176185 q = 0) : d177409 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176185, d177409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176185, d177409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176232 q = 0) : d177443 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176232, d177443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176232, d177443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16081 (p : Pattern) (selected : d176236 p = 0) : d177447 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176196 q = 0) : d177420 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176196, d177420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16072 q selected
    | true =>
      simp only [d176196, d177420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176197 q = 0) : d177421 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176197, d177421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176197, d177421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176154 q = 0) : d177378 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176154, d177378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16064 q selected
    | true =>
      simp only [d176154, d177378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176155 q = 0) : d177379 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176155, d177379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176155, d177379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176198 q = 0) : d177422 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176198, d177422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176198, d177422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176199 q = 0) : d177423 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176199, d177423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176199, d177423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176200 q = 0) : d177424 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176200, d177424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176200, d177424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176236 q = 0) : d177447 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176236, d177447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176236, d177447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16082 (p : Pattern) (selected : d176238 p = 0) : d177392 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176209 q = 0) : d177378 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176209, d177378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16075 q selected
    | true =>
      simp only [d176209, d177378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176210 q = 0) : d177379 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176210, d177379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176210, d177379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143108 q = 0) : d144416 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143108, d144416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12434 q selected
    | true =>
      simp only [d143108, d144416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143109 q = 0) : d144417 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143109, d144417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143109, d144417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176211 q = 0) : d177380 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176211, d177380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176211, d177380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176212 q = 0) : d177381 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176212, d177381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176212, d177381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176213 q = 0) : d177382 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176213, d177382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176213, d177382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176238 q = 0) : d177392 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176238, d177392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176238, d177392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16083 (p : Pattern) (selected : d176241 p = 0) : d177450 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176154 q = 0) : d177378 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176154, d177378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16064 q selected
    | true =>
      simp only [d176154, d177378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176155 q = 0) : d177379 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176155, d177379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176155, d177379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176217 q = 0) : d177428 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176217, d177428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176217, d177428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176218 q = 0) : d177429 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176218, d177429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176218, d177429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176219 q = 0) : d177430 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176219, d177430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176219, d177430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176241 q = 0) : d177450 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176241, d177450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176241, d177450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16084 (p : Pattern) (selected : d176247 p = 0) : d177456 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176180 q = 0) : d177404 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176180, d177404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16069 q selected
    | true =>
      simp only [d176180, d177404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12425 q selected
  have h2 (q : Pattern) (selected : d176181 q = 0) : d177405 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176181, d177405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176181, d177405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176182 q = 0) : d177406 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176182, d177406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176182, d177406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176183 q = 0) : d177407 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176183, d177407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176183, d177407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176187 q = 0) : d177411 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176187, d177411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16070 q selected
    | true =>
      simp only [d176187, d177411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12427 q selected
  have h6 (q : Pattern) (selected : d176188 q = 0) : d177412 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176188, d177412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176188, d177412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176189 q = 0) : d177413 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176189, d177413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176189, d177413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176202 q = 0) : d177426 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176202, d177426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16073 q selected
    | true =>
      simp only [d176202, d177426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16065 q selected
  have h9 (q : Pattern) (selected : d176215 q = 0) : d177384 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176215, d177384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16076 q selected
    | true =>
      simp only [d176215, d177384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12436 q selected
  have h10 (q : Pattern) (selected : d176216 q = 0) : d177427 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176216, d177427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d176216, d177427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d176221 q = 0) : d177432 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176221, d177432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16077 q selected
    | true =>
      simp only [d176221, d177432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d176222 q = 0) : d177433 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176222, d177433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d176222, d177433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d176223 q = 0) : d177434 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176223, d177434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d176223, d177434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d176224 q = 0) : d177435 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176224, d177435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176224, d177435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d176225 q = 0) : d177436 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176225, d177436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176225, d177436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d176228 q = 0) : d177439 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176228, d177439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16079 q selected
    | true =>
      simp only [d176228, d177439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12440 q selected
  have h17 (q : Pattern) (selected : d176229 q = 0) : d177440 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176229, d177440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176229, d177440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d176230 q = 0) : d177441 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176230, d177441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d176230, d177441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d176231 q = 0) : d177442 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176231, d177442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176231, d177442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d176233 q = 0) : d177444 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176233, d177444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16080 q selected
    | true =>
      simp only [d176233, d177444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12442 q selected
  have h21 (q : Pattern) (selected : d176234 q = 0) : d177445 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176234, d177445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176234, d177445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d176235 q = 0) : d177446 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176235, d177446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d176235, d177446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d176237 q = 0) : d177448 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176237, d177448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16081 q selected
    | true =>
      simp only [d176237, d177448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16067 q selected
  have h24 (q : Pattern) (selected : d176239 q = 0) : d177393 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176239, d177393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16082 q selected
    | true =>
      simp only [d176239, d177393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12445 q selected
  have h25 (q : Pattern) (selected : d176240 q = 0) : d177449 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176240, d177449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d176240, d177449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d176242 q = 0) : d177451 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176242, d177451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16083 q selected
    | true =>
      simp only [d176242, d177451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d176243 q = 0) : d177452 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176243, d177452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d176243, d177452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d176244 q = 0) : d177453 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176244, d177453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d176244, d177453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d176245 q = 0) : d177454 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176245, d177454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d176245, d177454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d176246 q = 0) : d177455 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176246, d177455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d176246, d177455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d176247 q = 0) : d177456 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176247, d177456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d176247, d177456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro16085 (p : Pattern) (selected : d176249 p = 0) : d177458 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176160 q = 0) : d177384 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176160, d177384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16065 q selected
    | true =>
      simp only [d176160, d177384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12419 q selected
  have h2 (q : Pattern) (selected : d176161 q = 0) : d177385 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176161, d177385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176161, d177385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176162 q = 0) : d177386 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176162, d177386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176162, d177386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176163 q = 0) : d177387 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176163, d177387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176163, d177387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176164 q = 0) : d177388 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176164, d177388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176164, d177388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143155 q = 0) : d144508 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d143155, d144508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12419 q selected
    | true =>
      simp only [d143155, d144508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d143156 q = 0) : d144509 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d143156, d144509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143156, d144509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143157 q = 0) : d144510 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d143157, d144510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d143157, d144510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d143158 q = 0) : d144511 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d143158, d144511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143158, d144511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d143159 q = 0) : d144512 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d143159, d144512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143159, d144512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d176249 q = 0) : d177458 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176249, d177458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176249, d177458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16086 (p : Pattern) (selected : d176256 p = 0) : d177465 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176237 q = 0) : d177448 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176237, d177448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16081 q selected
    | true =>
      simp only [d176237, d177448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16067 q selected
  have h2 (q : Pattern) (selected : d176239 q = 0) : d177393 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176239, d177393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16082 q selected
    | true =>
      simp only [d176239, d177393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12445 q selected
  have h3 (q : Pattern) (selected : d176240 q = 0) : d177449 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176240, d177449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d176240, d177449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176242 q = 0) : d177451 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176242, d177451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16083 q selected
    | true =>
      simp only [d176242, d177451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176243 q = 0) : d177452 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176243, d177452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176243, d177452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176244 q = 0) : d177453 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176244, d177453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176244, d177453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176254 q = 0) : d177463 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176254, d177463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176254, d177463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176255 q = 0) : d177464 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176255, d177464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176255, d177464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d176256 q = 0) : d177465 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176256, d177465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176256, d177465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro16087 (p : Pattern) (selected : d14647 p = 0) : d122850 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14644 q = 0) : d122847 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14644, d122847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14644, d122847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6642 q selected
  have h2 (q : Pattern) (selected : d9597 q = 0) : d101177 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9597, d101177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6642 q selected
    | true =>
      simp only [d9597, d101177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d14645 q = 0) : d122848 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14645, d122848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d14645, d122848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9599 q = 0) : d101179 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9599, d101179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9599, d101179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14646 q = 0) : d122849 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14646, d122849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14646, d122849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14647 q = 0) : d122850 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14647, d122850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14647, d122850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16088 (p : Pattern) (selected : d176271 p = 0) : d177480 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176262 q = 0) : d177471 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176262, d177471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16087 q selected
    | true =>
      simp only [d176262, d177471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16054 q selected
  have h2 (q : Pattern) (selected : d176263 q = 0) : d177472 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176263, d177472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176263, d177472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176264 q = 0) : d177473 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176264, d177473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176264, d177473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176265 q = 0) : d177474 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176265, d177474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16054 q selected
    | true =>
      simp only [d176265, d177474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12453 q selected
  have h5 (q : Pattern) (selected : d176266 q = 0) : d177475 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176266, d177475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176266, d177475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176267 q = 0) : d177476 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176267, d177476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176267, d177476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176268 q = 0) : d177477 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176268, d177477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176268, d177477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143188 q = 0) : d144541 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143188, d144541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12453 q selected
    | true =>
      simp only [d143188, d144541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d143189 q = 0) : d144542 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143189, d144542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143189, d144542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d143190 q = 0) : d144543 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143190, d144543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143190, d144543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d176269 q = 0) : d177478 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176269, d177478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176269, d177478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d176270 q = 0) : d177479 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176270, d177479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176270, d177479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d176271 q = 0) : d177480 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176271, d177480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d176271, d177480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro16089 (p : Pattern) (selected : d176275 p = 0) : d177484 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176265 q = 0) : d177474 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176265, d177474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16054 q selected
    | true =>
      simp only [d176265, d177474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12453 q selected
  have h2 (q : Pattern) (selected : d176266 q = 0) : d177475 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176266, d177475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176266, d177475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176267 q = 0) : d177476 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176267, d177476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176267, d177476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143188 q = 0) : d144541 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143188, d144541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12453 q selected
    | true =>
      simp only [d143188, d144541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143189 q = 0) : d144542 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143189, d144542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143189, d144542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143190 q = 0) : d144543 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143190, d144543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143190, d144543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176269 q = 0) : d177478 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176269, d177478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176269, d177478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143196 q = 0) : d144549 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143196, d144549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143196, d144549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d176274 q = 0) : d177483 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176274, d177483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176274, d177483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176275 q = 0) : d177484 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176275, d177484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d176275, d177484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16090 (p : Pattern) (selected : d176281 p = 0) : d177490 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176272 q = 0) : d177481 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176272, d177481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16088 q selected
    | true =>
      simp only [d176272, d177481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176273 q = 0) : d177482 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176273, d177482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176273, d177482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176276 q = 0) : d177485 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176276, d177485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16089 q selected
    | true =>
      simp only [d176276, d177485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176277 q = 0) : d177486 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176277, d177486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176277, d177486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176278 q = 0) : d177487 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176278, d177487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176278, d177487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176279 q = 0) : d177488 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176279, d177488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176279, d177488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176280 q = 0) : d177489 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176280, d177489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176280, d177489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176281 q = 0) : d177490 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176281, d177490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176281, d177490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16091 (p : Pattern) (selected : d176285 p = 0) : d177494 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176276 q = 0) : d177485 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176276, d177485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16089 q selected
    | true =>
      simp only [d176276, d177485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176277 q = 0) : d177486 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176277, d177486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176277, d177486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143207 q = 0) : d144560 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143207, d144560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12457 q selected
    | true =>
      simp only [d143207, d144560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143208 q = 0) : d144561 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143208, d144561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143208, d144561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176282 q = 0) : d177491 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176282, d177491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176282, d177491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176283 q = 0) : d177492 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176283, d177492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176283, d177492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176284 q = 0) : d177493 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176284, d177493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176284, d177493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176285 q = 0) : d177494 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176285, d177494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176285, d177494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16092 (p : Pattern) (selected : d14692 p = 0) : d113217 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14689 q = 0) : d113214 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14689, d113214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14689, d113214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6655 q selected
  have h2 (q : Pattern) (selected : d9671 q = 0) : d101083 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9671, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6655 q selected
    | true =>
      simp only [d9671, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d14690 q = 0) : d113215 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14690, d113215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d14690, d113215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9673 q = 0) : d101085 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9673, d101085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9673, d101085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14691 q = 0) : d113216 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14691, d113216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14691, d113216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14692 q = 0) : d113217 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14692, d113217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14692, d113217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16093 (p : Pattern) (selected : d176292 p = 0) : d177484 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176287 q = 0) : d177474 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176287, d177474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16092 q selected
    | true =>
      simp only [d176287, d177474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12460 q selected
  have h2 (q : Pattern) (selected : d176288 q = 0) : d177475 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176288, d177475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176288, d177475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176289 q = 0) : d177476 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176289, d177476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176289, d177476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143217 q = 0) : d144541 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143217, d144541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12460 q selected
    | true =>
      simp only [d143217, d144541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143218 q = 0) : d144542 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143218, d144542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143218, d144542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143219 q = 0) : d144543 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143219, d144543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143219, d144543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176290 q = 0) : d177478 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176290, d177478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176290, d177478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143221 q = 0) : d144549 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143221, d144549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143221, d144549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d176291 q = 0) : d177483 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176291, d177483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176291, d177483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176292 q = 0) : d177484 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176292, d177484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d176292, d177484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16094 (p : Pattern) (selected : d176298 p = 0) : d177494 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176293 q = 0) : d177485 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176293, d177485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16093 q selected
    | true =>
      simp only [d176293, d177485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176294 q = 0) : d177486 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176294, d177486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176294, d177486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143228 q = 0) : d144560 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143228, d144560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12462 q selected
    | true =>
      simp only [d143228, d144560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143229 q = 0) : d144561 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143229, d144561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143229, d144561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176295 q = 0) : d177491 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176295, d177491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176295, d177491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176296 q = 0) : d177492 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176296, d177492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176296, d177492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176297 q = 0) : d177493 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176297, d177493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176297, d177493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176298 q = 0) : d177494 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176298, d177494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176298, d177494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16095 (p : Pattern) (selected : d176304 p = 0) : d177501 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176276 q = 0) : d177485 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176276, d177485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16089 q selected
    | true =>
      simp only [d176276, d177485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176277 q = 0) : d177486 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176277, d177486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176277, d177486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176301 q = 0) : d177498 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176301, d177498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176301, d177498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176302 q = 0) : d177499 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176302, d177499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176302, d177499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176303 q = 0) : d177500 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176303, d177500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176303, d177500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176304 q = 0) : d177501 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176304, d177501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176304, d177501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16096 (p : Pattern) (selected : d176310 p = 0) : d177507 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176286 q = 0) : d177495 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176286, d177495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16090 q selected
    | true =>
      simp only [d176286, d177495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16091 q selected
  have h2 (q : Pattern) (selected : d176299 q = 0) : d177496 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176299, d177496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16094 q selected
    | true =>
      simp only [d176299, d177496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12464 q selected
  have h3 (q : Pattern) (selected : d176300 q = 0) : d177497 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176300, d177497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d176300, d177497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176305 q = 0) : d177502 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176305, d177502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16095 q selected
    | true =>
      simp only [d176305, d177502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176306 q = 0) : d177503 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176306, d177503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176306, d177503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176307 q = 0) : d177504 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176307, d177504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176307, d177504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176308 q = 0) : d177505 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176308, d177505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176308, d177505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176309 q = 0) : d177506 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176309, d177506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176309, d177506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d176310 q = 0) : d177507 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176310, d177507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176310, d177507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro16097 (p : Pattern) (selected : d176316 p = 0) : d177513 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176166 q = 0) : d177390 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d176166, d177390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176166, d177390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16066 q selected
  have h2 (q : Pattern) (selected : d176167 q = 0) : d177391 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d176167, d177391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d176167, d177391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d176175 q = 0) : d177399 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d176175, d177399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16066 q selected
    | true =>
      simp only [d176175, d177399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16068 q selected
  have h4 (q : Pattern) (selected : d176176 q = 0) : d177400 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d176176, d177400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176176, d177400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176177 q = 0) : d177401 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d176177, d177401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176177, d177401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176248 q = 0) : d177457 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d176248, d177457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16078 q selected
    | true =>
      simp only [d176248, d177457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16084 q selected
  have h7 (q : Pattern) (selected : d176250 q = 0) : d177459 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d176250, d177459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16085 q selected
    | true =>
      simp only [d176250, d177459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12449 q selected
  have h8 (q : Pattern) (selected : d176251 q = 0) : d177460 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d176251, d177460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176251, d177460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d176252 q = 0) : d177461 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d176252, d177461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d176252, d177461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d176253 q = 0) : d177462 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d176253, d177462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176253, d177462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d176257 q = 0) : d177466 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d176257, d177466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176257, d177466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16086 q selected
  have h12 (q : Pattern) (selected : d143176 q = 0) : d144529 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d143176, d144529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143176, d144529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12451 q selected
  have h13 (q : Pattern) (selected : d176258 q = 0) : d177467 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d176258, d177467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d176258, d177467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d176259 q = 0) : d177468 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d176259, d177468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d176259, d177468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d176260 q = 0) : d177469 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d176260, d177469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d176260, d177469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d176261 q = 0) : d177470 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d176261, d177470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d176261, d177470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d176311 q = 0) : d177508 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d176311, d177508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176311, d177508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16096 q selected
  have h18 (q : Pattern) (selected : d143261 q = 0) : d144590 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d143261, d144590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143261, d144590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12468 q selected
  have h19 (q : Pattern) (selected : d176312 q = 0) : d177509 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d176312, d177509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d176312, d177509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d176313 q = 0) : d177510 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d176313, d177510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d176313, d177510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d176314 q = 0) : d177511 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d176314, d177511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d176314, d177511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d176315 q = 0) : d177512 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d176315, d177512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d176315, d177512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d176316 q = 0) : d177513 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d176316, d177513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d176316, d177513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro16098 (p : Pattern) (selected : d176322 p = 0) : d177519 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176317 q = 0) : d177514 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d176317, d177514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176317, d177514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16097 q selected
  have h2 (q : Pattern) (selected : d176318 q = 0) : d177515 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d176318, d177515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176318, d177515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176319 q = 0) : d177516 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d176319, d177516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176319, d177516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176320 q = 0) : d177517 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d176320, d177517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176320, d177517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176321 q = 0) : d177518 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d176321, d177518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176321, d177518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176322 q = 0) : d177519 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d176322, d177519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176322, d177519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16099 (p : Pattern) (selected : d14759 p = 0) : d122930 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d9778 q = 0) : d101299 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9778, d101299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6672 q selected
    | true =>
      simp only [d9778, d101299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9780 q = 0) : d101301 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9780, d101301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9780, d101301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d14758 q = 0) : d122929 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14758, d122929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14758, d122929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d14759 q = 0) : d122930 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14759, d122930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14759, d122930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16100 (p : Pattern) (selected : d14764 p = 0) : d122935 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d9800 q = 0) : d101321 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6675 q selected
    | true =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9802 q = 0) : d101323 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9802, d101323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9802, d101323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d14763 q = 0) : d122934 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14763, d122934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14763, d122934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d14764 q = 0) : d122935 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14764, d122935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14764, d122935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16101 (p : Pattern) (selected : d14771 p = 0) : d122942 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d9844 q = 0) : d101365 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6680 q selected
    | true =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9846 q = 0) : d101367 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9846, d101367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9846, d101367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d14770 q = 0) : d122941 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14770, d122941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14770, d122941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d14771 q = 0) : d122942 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14771, d122942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14771, d122942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16102 (p : Pattern) (selected : d176334 p = 0) : d177531 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176325 q = 0) : d177522 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176325, d177522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16099 q selected
    | true =>
      simp only [d176325, d177522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16100 q selected
  have h2 (q : Pattern) (selected : d176326 q = 0) : d177523 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176326, d177523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176326, d177523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176327 q = 0) : d177524 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176327, d177524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176327, d177524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176328 q = 0) : d177525 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176328, d177525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16100 q selected
    | true =>
      simp only [d176328, d177525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16101 q selected
  have h5 (q : Pattern) (selected : d176329 q = 0) : d177526 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176329, d177526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176329, d177526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176330 q = 0) : d177527 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176330, d177527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176330, d177527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176331 q = 0) : d177528 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176331, d177528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176331, d177528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176332 q = 0) : d177529 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176332, d177529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176332, d177529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d176333 q = 0) : d177530 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176333, d177530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176333, d177530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176334 q = 0) : d177531 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176334, d177531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d176334, d177531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16103 (p : Pattern) (selected : d176338 p = 0) : d177535 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176328 q = 0) : d177525 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176328, d177525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16100 q selected
    | true =>
      simp only [d176328, d177525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16101 q selected
  have h2 (q : Pattern) (selected : d176329 q = 0) : d177526 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176329, d177526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176329, d177526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176330 q = 0) : d177527 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176330, d177527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176330, d177527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176332 q = 0) : d177529 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176332, d177529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176332, d177529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176337 q = 0) : d177534 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176337, d177534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176337, d177534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176338 q = 0) : d177535 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176338, d177535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176338, d177535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16104 (p : Pattern) (selected : d176344 p = 0) : d177541 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176335 q = 0) : d177532 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176335, d177532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16102 q selected
    | true =>
      simp only [d176335, d177532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176336 q = 0) : d177533 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176336, d177533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176336, d177533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176339 q = 0) : d177536 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176339, d177536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16103 q selected
    | true =>
      simp only [d176339, d177536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176340 q = 0) : d177537 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176340, d177537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176340, d177537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176341 q = 0) : d177538 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176341, d177538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176341, d177538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176342 q = 0) : d177539 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176342, d177539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176342, d177539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176343 q = 0) : d177540 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176343, d177540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176343, d177540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176344 q = 0) : d177541 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176344, d177541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176344, d177541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16105 (p : Pattern) (selected : d176348 p = 0) : d177545 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176339 q = 0) : d177536 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176339, d177536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16103 q selected
    | true =>
      simp only [d176339, d177536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176340 q = 0) : d177537 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176340, d177537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176340, d177537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176345 q = 0) : d177542 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176345, d177542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176345, d177542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176346 q = 0) : d177543 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176346, d177543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176346, d177543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176347 q = 0) : d177544 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176347, d177544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176347, d177544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176348 q = 0) : d177545 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176348, d177545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176348, d177545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16106 (p : Pattern) (selected : d176354 p = 0) : d177551 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176349 q = 0) : d177546 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176349, d177546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16104 q selected
    | true =>
      simp only [d176349, d177546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16105 q selected
  have h2 (q : Pattern) (selected : d176350 q = 0) : d177547 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176350, d177547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176350, d177547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176351 q = 0) : d177548 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176351, d177548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176351, d177548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176352 q = 0) : d177549 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176352, d177549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176352, d177549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176353 q = 0) : d177550 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176353, d177550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176353, d177550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176354 q = 0) : d177551 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176354, d177551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176354, d177551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16107 (p : Pattern) (selected : d176357 p = 0) : d177554 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176335 q = 0) : d177532 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176335, d177532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16102 q selected
    | true =>
      simp only [d176335, d177532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176336 q = 0) : d177533 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176336, d177533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176336, d177533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176339 q = 0) : d177536 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176339, d177536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16103 q selected
    | true =>
      simp only [d176339, d177536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176340 q = 0) : d177537 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176340, d177537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176340, d177537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176341 q = 0) : d177538 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176341, d177538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176341, d177538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176342 q = 0) : d177539 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176342, d177539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176342, d177539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176343 q = 0) : d177540 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176343, d177540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176343, d177540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176357 q = 0) : d177554 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176357, d177554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176357, d177554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16108 (p : Pattern) (selected : d176358 p = 0) : d177555 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176339 q = 0) : d177536 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176339, d177536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16103 q selected
    | true =>
      simp only [d176339, d177536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176340 q = 0) : d177537 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176340, d177537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176340, d177537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176345 q = 0) : d177542 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176345, d177542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176345, d177542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176346 q = 0) : d177543 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176346, d177543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176346, d177543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176347 q = 0) : d177544 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176347, d177544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176347, d177544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176358 q = 0) : d177555 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176358, d177555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176358, d177555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16109 (p : Pattern) (selected : d176364 p = 0) : d177561 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176349 q = 0) : d177546 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176349, d177546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16104 q selected
    | true =>
      simp only [d176349, d177546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16105 q selected
  have h2 (q : Pattern) (selected : d176350 q = 0) : d177547 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176350, d177547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176350, d177547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176351 q = 0) : d177548 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176351, d177548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176351, d177548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176352 q = 0) : d177549 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176352, d177549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176352, d177549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176353 q = 0) : d177550 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176353, d177550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176353, d177550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176359 q = 0) : d177556 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176359, d177556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16107 q selected
    | true =>
      simp only [d176359, d177556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16108 q selected
  have h7 (q : Pattern) (selected : d176360 q = 0) : d177557 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176360, d177557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176360, d177557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176361 q = 0) : d177558 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176361, d177558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176361, d177558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d176362 q = 0) : d177559 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176362, d177559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176362, d177559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176363 q = 0) : d177560 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176363, d177560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176363, d177560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d176364 q = 0) : d177561 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176364, d177561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176364, d177561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16110 (p : Pattern) (selected : d176369 p = 0) : d177566 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176335 q = 0) : d177532 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176335, d177532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16102 q selected
    | true =>
      simp only [d176335, d177532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176336 q = 0) : d177533 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176336, d177533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176336, d177533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176339 q = 0) : d177536 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176339, d177536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16103 q selected
    | true =>
      simp only [d176339, d177536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176340 q = 0) : d177537 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176340, d177537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176340, d177537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176341 q = 0) : d177538 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176341, d177538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176341, d177538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176342 q = 0) : d177539 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176342, d177539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176342, d177539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176368 q = 0) : d177565 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176368, d177565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176368, d177565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176369 q = 0) : d177566 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176369, d177566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176369, d177566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16111 (p : Pattern) (selected : d176371 p = 0) : d177568 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176339 q = 0) : d177536 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176339, d177536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16103 q selected
    | true =>
      simp only [d176339, d177536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176340 q = 0) : d177537 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176340, d177537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176340, d177537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176345 q = 0) : d177542 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176345, d177542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176345, d177542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176346 q = 0) : d177543 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176346, d177543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176346, d177543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176370 q = 0) : d177567 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176370, d177567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176370, d177567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176371 q = 0) : d177568 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176371, d177568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176371, d177568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16112 (p : Pattern) (selected : d176378 p = 0) : d177575 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176335 q = 0) : d177532 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176335, d177532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16102 q selected
    | true =>
      simp only [d176335, d177532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176336 q = 0) : d177533 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176336, d177533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176336, d177533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176339 q = 0) : d177536 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176339, d177536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16103 q selected
    | true =>
      simp only [d176339, d177536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176340 q = 0) : d177537 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176340, d177537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176340, d177537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176341 q = 0) : d177538 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176341, d177538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176341, d177538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176376 q = 0) : d177573 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176376, d177573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176376, d177573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176377 q = 0) : d177574 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176377, d177574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176377, d177574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176378 q = 0) : d177575 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176378, d177575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176378, d177575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16113 (p : Pattern) (selected : d176381 p = 0) : d177578 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176339 q = 0) : d177536 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176339, d177536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16103 q selected
    | true =>
      simp only [d176339, d177536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176340 q = 0) : d177537 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176340, d177537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176340, d177537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176345 q = 0) : d177542 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176345, d177542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176345, d177542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176379 q = 0) : d177576 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176379, d177576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176379, d177576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176380 q = 0) : d177577 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176380, d177577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176380, d177577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176381 q = 0) : d177578 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176381, d177578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176381, d177578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16114 (p : Pattern) (selected : d14837 p = 0) : d123008 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d9763 q = 0) : d101284 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9763, d101284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6670 q selected
    | true =>
      simp only [d9763, d101284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9765 q = 0) : d101286 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9765, d101286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9765, d101286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d14836 q = 0) : d123007 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14836, d123007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14836, d123007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d14837 q = 0) : d123008 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14837, d123008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14837, d123008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16115 (p : Pattern) (selected : d176390 p = 0) : d177587 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176385 q = 0) : d177582 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176385, d177582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16114 q selected
    | true =>
      simp only [d176385, d177582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16099 q selected
  have h2 (q : Pattern) (selected : d176386 q = 0) : d177583 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176386, d177583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176386, d177583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176387 q = 0) : d177584 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176387, d177584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176387, d177584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176325 q = 0) : d177522 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176325, d177522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16099 q selected
    | true =>
      simp only [d176325, d177522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16100 q selected
  have h5 (q : Pattern) (selected : d176326 q = 0) : d177523 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176326, d177523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176326, d177523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176327 q = 0) : d177524 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176327, d177524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176327, d177524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176388 q = 0) : d177585 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176388, d177585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176388, d177585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176328 q = 0) : d177525 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176328, d177525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16100 q selected
    | true =>
      simp only [d176328, d177525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16101 q selected
  have h9 (q : Pattern) (selected : d176329 q = 0) : d177526 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176329, d177526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176329, d177526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176330 q = 0) : d177527 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176330, d177527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176330, d177527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d176331 q = 0) : d177528 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176331, d177528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176331, d177528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d176389 q = 0) : d177586 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176389, d177586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176389, d177586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d176390 q = 0) : d177587 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176390, d177587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d176390, d177587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro16116 (p : Pattern) (selected : d176396 p = 0) : d177593 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176391 q = 0) : d177588 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176391, d177588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16115 q selected
    | true =>
      simp only [d176391, d177588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176392 q = 0) : d177589 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176392, d177589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176392, d177589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176335 q = 0) : d177532 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176335, d177532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16102 q selected
    | true =>
      simp only [d176335, d177532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176336 q = 0) : d177533 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176336, d177533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176336, d177533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176393 q = 0) : d177590 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176393, d177590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176393, d177590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176394 q = 0) : d177591 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176394, d177591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176394, d177591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176395 q = 0) : d177592 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176395, d177592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176395, d177592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176396 q = 0) : d177593 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176396, d177593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176396, d177593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16117 (p : Pattern) (selected : d14869 p = 0) : d122930 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d9908 q = 0) : d101299 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9908, d101299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6691 q selected
    | true =>
      simp only [d9908, d101299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9910 q = 0) : d101301 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9910, d101301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9910, d101301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d14868 q = 0) : d122929 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14868, d122929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14868, d122929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d14869 q = 0) : d122930 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14869, d122930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14869, d122930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16118 (p : Pattern) (selected : d14874 p = 0) : d122935 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d9918 q = 0) : d101321 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9918, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6692 q selected
    | true =>
      simp only [d9918, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9920 q = 0) : d101323 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9920, d101323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9920, d101323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d14873 q = 0) : d122934 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14873, d122934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14873, d122934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d14874 q = 0) : d122935 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14874, d122935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14874, d122935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16119 (p : Pattern) (selected : d14881 p = 0) : d122942 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d9952 q = 0) : d101365 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9952, d101365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6696 q selected
    | true =>
      simp only [d9952, d101365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9954 q = 0) : d101367 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9954, d101367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9954, d101367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d14880 q = 0) : d122941 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14880, d122941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14880, d122941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d14881 q = 0) : d122942 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14881, d122942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14881, d122942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16120 (p : Pattern) (selected : d176407 p = 0) : d177531 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176398 q = 0) : d177522 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176398, d177522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16117 q selected
    | true =>
      simp only [d176398, d177522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16118 q selected
  have h2 (q : Pattern) (selected : d176399 q = 0) : d177523 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176399, d177523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176399, d177523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176400 q = 0) : d177524 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176400, d177524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176400, d177524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176401 q = 0) : d177525 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176401, d177525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16118 q selected
    | true =>
      simp only [d176401, d177525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16119 q selected
  have h5 (q : Pattern) (selected : d176402 q = 0) : d177526 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176402, d177526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176402, d177526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176403 q = 0) : d177527 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176403, d177527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176403, d177527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176404 q = 0) : d177528 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176404, d177528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176404, d177528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176405 q = 0) : d177529 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176405, d177529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176405, d177529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d176406 q = 0) : d177530 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176406, d177530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176406, d177530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176407 q = 0) : d177531 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176407, d177531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d176407, d177531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16121 (p : Pattern) (selected : d176411 p = 0) : d177535 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176401 q = 0) : d177525 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176401, d177525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16118 q selected
    | true =>
      simp only [d176401, d177525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16119 q selected
  have h2 (q : Pattern) (selected : d176402 q = 0) : d177526 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176402, d177526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176402, d177526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176403 q = 0) : d177527 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176403, d177527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176403, d177527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176405 q = 0) : d177529 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176405, d177529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176405, d177529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176410 q = 0) : d177534 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176410, d177534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176410, d177534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176411 q = 0) : d177535 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176411, d177535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176411, d177535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16122 (p : Pattern) (selected : d176417 p = 0) : d177541 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176408 q = 0) : d177532 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176408, d177532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16120 q selected
    | true =>
      simp only [d176408, d177532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176409 q = 0) : d177533 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176409, d177533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176409, d177533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176412 q = 0) : d177536 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176412, d177536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16121 q selected
    | true =>
      simp only [d176412, d177536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176413 q = 0) : d177537 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176413, d177537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176413, d177537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176414 q = 0) : d177538 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176414, d177538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176414, d177538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176415 q = 0) : d177539 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176415, d177539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176415, d177539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176416 q = 0) : d177540 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176416, d177540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176416, d177540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176417 q = 0) : d177541 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176417, d177541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176417, d177541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16123 (p : Pattern) (selected : d176421 p = 0) : d177545 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176412 q = 0) : d177536 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176412, d177536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16121 q selected
    | true =>
      simp only [d176412, d177536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176413 q = 0) : d177537 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176413, d177537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176413, d177537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176418 q = 0) : d177542 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176418, d177542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176418, d177542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176419 q = 0) : d177543 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176419, d177543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176419, d177543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176420 q = 0) : d177544 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176420, d177544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176420, d177544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176421 q = 0) : d177545 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176421, d177545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176421, d177545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16124 (p : Pattern) (selected : d176429 p = 0) : d177601 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176325 q = 0) : d177522 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176325, d177522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16099 q selected
    | true =>
      simp only [d176325, d177522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16100 q selected
  have h2 (q : Pattern) (selected : d176326 q = 0) : d177523 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176326, d177523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176326, d177523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176327 q = 0) : d177524 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176327, d177524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176327, d177524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176328 q = 0) : d177525 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176328, d177525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16100 q selected
    | true =>
      simp only [d176328, d177525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16101 q selected
  have h5 (q : Pattern) (selected : d176329 q = 0) : d177526 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176329, d177526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176329, d177526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176330 q = 0) : d177527 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176330, d177527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176330, d177527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176331 q = 0) : d177528 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176331, d177528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176331, d177528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176424 q = 0) : d177596 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176424, d177596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16100 q selected
    | true =>
      simp only [d176424, d177596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d176425 q = 0) : d177597 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176425, d177597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176425, d177597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176426 q = 0) : d177598 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176426, d177598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176426, d177598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d176427 q = 0) : d177599 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176427, d177599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d176427, d177599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d176428 q = 0) : d177600 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176428, d177600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176428, d177600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d176429 q = 0) : d177601 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176429, d177601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d176429, d177601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro16125 (p : Pattern) (selected : d176435 p = 0) : d177607 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176430 q = 0) : d177602 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176430, d177602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16124 q selected
    | true =>
      simp only [d176430, d177602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176431 q = 0) : d177603 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176431, d177603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176431, d177603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176432 q = 0) : d177604 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176432, d177604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176432, d177604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176433 q = 0) : d177605 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176433, d177605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176433, d177605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176434 q = 0) : d177606 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176434, d177606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176434, d177606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176435 q = 0) : d177607 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176435, d177607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176435, d177607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16126 (p : Pattern) (selected : d176441 p = 0) : d177613 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176372 q = 0) : d177569 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176372, d177569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16110 q selected
    | true =>
      simp only [d176372, d177569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16111 q selected
  have h2 (q : Pattern) (selected : d176373 q = 0) : d177570 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176373, d177570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176373, d177570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176374 q = 0) : d177571 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176374, d177571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176374, d177571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176375 q = 0) : d177572 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176375, d177572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176375, d177572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176382 q = 0) : d177579 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176382, d177579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16112 q selected
    | true =>
      simp only [d176382, d177579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16113 q selected
  have h6 (q : Pattern) (selected : d176383 q = 0) : d177580 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176383, d177580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176383, d177580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176384 q = 0) : d177581 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176384, d177581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176384, d177581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176397 q = 0) : d177594 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176397, d177594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16116 q selected
    | true =>
      simp only [d176397, d177594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16104 q selected
  have h9 (q : Pattern) (selected : d176422 q = 0) : d177546 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176422, d177546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16122 q selected
    | true =>
      simp only [d176422, d177546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16123 q selected
  have h10 (q : Pattern) (selected : d176423 q = 0) : d177595 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176423, d177595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d176423, d177595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d176436 q = 0) : d177608 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176436, d177608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16125 q selected
    | true =>
      simp only [d176436, d177608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d176437 q = 0) : d177609 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176437, d177609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d176437, d177609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d176438 q = 0) : d177610 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176438, d177610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d176438, d177610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d176439 q = 0) : d177611 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176439, d177611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176439, d177611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d176440 q = 0) : d177612 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176440, d177612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176440, d177612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d176441 q = 0) : d177613 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176441, d177613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176441, d177613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro16127 (p : Pattern) (selected : d176442 p = 0) : d177614 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176335 q = 0) : d177532 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176335, d177532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16102 q selected
    | true =>
      simp only [d176335, d177532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176336 q = 0) : d177533 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176336, d177533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176336, d177533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176339 q = 0) : d177536 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176339, d177536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16103 q selected
    | true =>
      simp only [d176339, d177536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176340 q = 0) : d177537 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176340, d177537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176340, d177537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176341 q = 0) : d177538 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176341, d177538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176341, d177538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176342 q = 0) : d177539 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176342, d177539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176342, d177539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176368 q = 0) : d177565 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176368, d177565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176368, d177565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176442 q = 0) : d177614 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176442, d177614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176442, d177614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16128 (p : Pattern) (selected : d176443 p = 0) : d177615 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176339 q = 0) : d177536 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176339, d177536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16103 q selected
    | true =>
      simp only [d176339, d177536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176340 q = 0) : d177537 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176340, d177537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176340, d177537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176345 q = 0) : d177542 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176345, d177542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176345, d177542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176346 q = 0) : d177543 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176346, d177543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176346, d177543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176370 q = 0) : d177567 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176370, d177567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176370, d177567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176443 q = 0) : d177615 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176443, d177615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176443, d177615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16129 (p : Pattern) (selected : d176448 p = 0) : d177620 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176335 q = 0) : d177532 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176335, d177532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16102 q selected
    | true =>
      simp only [d176335, d177532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176336 q = 0) : d177533 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176336, d177533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176336, d177533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176339 q = 0) : d177536 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176339, d177536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16103 q selected
    | true =>
      simp only [d176339, d177536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176340 q = 0) : d177537 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176340, d177537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176340, d177537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176341 q = 0) : d177538 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176341, d177538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176341, d177538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176376 q = 0) : d177573 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176376, d177573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176376, d177573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176377 q = 0) : d177574 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176377, d177574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176377, d177574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176448 q = 0) : d177620 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176448, d177620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176448, d177620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16130 (p : Pattern) (selected : d176449 p = 0) : d177621 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176339 q = 0) : d177536 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176339, d177536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16103 q selected
    | true =>
      simp only [d176339, d177536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176340 q = 0) : d177537 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176340, d177537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176340, d177537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176345 q = 0) : d177542 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176345, d177542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176345, d177542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176379 q = 0) : d177576 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176379, d177576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176379, d177576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176380 q = 0) : d177577 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176380, d177577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176380, d177577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176449 q = 0) : d177621 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176449, d177621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176449, d177621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16131 (p : Pattern) (selected : d176453 p = 0) : d177625 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176391 q = 0) : d177588 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176391, d177588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16115 q selected
    | true =>
      simp only [d176391, d177588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176392 q = 0) : d177589 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176392, d177589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176392, d177589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176335 q = 0) : d177532 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176335, d177532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16102 q selected
    | true =>
      simp only [d176335, d177532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176336 q = 0) : d177533 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176336, d177533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176336, d177533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176393 q = 0) : d177590 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176393, d177590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176393, d177590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176394 q = 0) : d177591 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176394, d177591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176394, d177591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176395 q = 0) : d177592 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176395, d177592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176395, d177592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176453 q = 0) : d177625 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176453, d177625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176453, d177625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16132 (p : Pattern) (selected : d176455 p = 0) : d177554 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176408 q = 0) : d177532 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176408, d177532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16120 q selected
    | true =>
      simp only [d176408, d177532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176409 q = 0) : d177533 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176409, d177533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176409, d177533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176412 q = 0) : d177536 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176412, d177536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16121 q selected
    | true =>
      simp only [d176412, d177536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176413 q = 0) : d177537 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176413, d177537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176413, d177537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176414 q = 0) : d177538 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176414, d177538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176414, d177538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176415 q = 0) : d177539 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176415, d177539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176415, d177539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176416 q = 0) : d177540 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176416, d177540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176416, d177540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176455 q = 0) : d177554 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176455, d177554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176455, d177554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16133 (p : Pattern) (selected : d176456 p = 0) : d177555 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176412 q = 0) : d177536 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176412, d177536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16121 q selected
    | true =>
      simp only [d176412, d177536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176413 q = 0) : d177537 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176413, d177537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176413, d177537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176418 q = 0) : d177542 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176418, d177542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176418, d177542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176419 q = 0) : d177543 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176419, d177543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176419, d177543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176420 q = 0) : d177544 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176420, d177544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176420, d177544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176456 q = 0) : d177555 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176456, d177555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176456, d177555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16134 (p : Pattern) (selected : d176459 p = 0) : d177628 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176430 q = 0) : d177602 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176430, d177602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16124 q selected
    | true =>
      simp only [d176430, d177602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176431 q = 0) : d177603 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176431, d177603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176431, d177603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176432 q = 0) : d177604 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176432, d177604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176432, d177604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176433 q = 0) : d177605 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176433, d177605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176433, d177605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176434 q = 0) : d177606 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176434, d177606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176434, d177606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176459 q = 0) : d177628 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176459, d177628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176459, d177628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16135 (p : Pattern) (selected : d176465 p = 0) : d177634 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176372 q = 0) : d177569 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176372, d177569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16110 q selected
    | true =>
      simp only [d176372, d177569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16111 q selected
  have h2 (q : Pattern) (selected : d176373 q = 0) : d177570 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176373, d177570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176373, d177570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176374 q = 0) : d177571 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176374, d177571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176374, d177571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176375 q = 0) : d177572 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176375, d177572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176375, d177572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176382 q = 0) : d177579 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176382, d177579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16112 q selected
    | true =>
      simp only [d176382, d177579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16113 q selected
  have h6 (q : Pattern) (selected : d176383 q = 0) : d177580 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176383, d177580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176383, d177580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176384 q = 0) : d177581 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176384, d177581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176384, d177581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176397 q = 0) : d177594 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176397, d177594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16116 q selected
    | true =>
      simp only [d176397, d177594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16104 q selected
  have h9 (q : Pattern) (selected : d176422 q = 0) : d177546 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176422, d177546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16122 q selected
    | true =>
      simp only [d176422, d177546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16123 q selected
  have h10 (q : Pattern) (selected : d176423 q = 0) : d177595 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176423, d177595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d176423, d177595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d176436 q = 0) : d177608 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176436, d177608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16125 q selected
    | true =>
      simp only [d176436, d177608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d176437 q = 0) : d177609 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176437, d177609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d176437, d177609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d176438 q = 0) : d177610 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176438, d177610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d176438, d177610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d176439 q = 0) : d177611 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176439, d177611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176439, d177611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d176440 q = 0) : d177612 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176440, d177612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176440, d177612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d176444 q = 0) : d177616 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176444, d177616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16127 q selected
    | true =>
      simp only [d176444, d177616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16128 q selected
  have h17 (q : Pattern) (selected : d176445 q = 0) : d177617 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176445, d177617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176445, d177617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d176446 q = 0) : d177618 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176446, d177618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d176446, d177618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d176447 q = 0) : d177619 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176447, d177619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176447, d177619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d176450 q = 0) : d177622 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176450, d177622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16129 q selected
    | true =>
      simp only [d176450, d177622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16130 q selected
  have h21 (q : Pattern) (selected : d176451 q = 0) : d177623 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176451, d177623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176451, d177623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d176452 q = 0) : d177624 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176452, d177624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d176452, d177624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d176454 q = 0) : d177626 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176454, d177626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16131 q selected
    | true =>
      simp only [d176454, d177626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16107 q selected
  have h24 (q : Pattern) (selected : d176457 q = 0) : d177556 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176457, d177556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16132 q selected
    | true =>
      simp only [d176457, d177556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16133 q selected
  have h25 (q : Pattern) (selected : d176458 q = 0) : d177627 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176458, d177627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d176458, d177627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d176460 q = 0) : d177629 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176460, d177629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16134 q selected
    | true =>
      simp only [d176460, d177629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d176461 q = 0) : d177630 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176461, d177630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d176461, d177630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d176462 q = 0) : d177631 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176462, d177631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d176462, d177631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d176463 q = 0) : d177632 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176463, d177632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d176463, d177632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d176464 q = 0) : d177633 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176464, d177633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d176464, d177633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d176465 q = 0) : d177634 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176465, d177634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d176465, d177634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro16136 (p : Pattern) (selected : d176472 p = 0) : d177641 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176349 q = 0) : d177546 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176349, d177546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16104 q selected
    | true =>
      simp only [d176349, d177546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16105 q selected
  have h2 (q : Pattern) (selected : d176350 q = 0) : d177547 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176350, d177547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176350, d177547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176351 q = 0) : d177548 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176351, d177548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176351, d177548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176352 q = 0) : d177549 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176352, d177549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176352, d177549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176353 q = 0) : d177550 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176353, d177550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176353, d177550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176467 q = 0) : d177636 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176467, d177636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16105 q selected
    | true =>
      simp only [d176467, d177636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176468 q = 0) : d177637 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176468, d177637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176468, d177637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176469 q = 0) : d177638 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176469, d177638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176469, d177638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d176470 q = 0) : d177639 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176470, d177639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176470, d177639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176471 q = 0) : d177640 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176471, d177640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176471, d177640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d176472 q = 0) : d177641 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176472, d177641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176472, d177641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16137 (p : Pattern) (selected : d176478 p = 0) : d177647 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176467 q = 0) : d177636 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176467, d177636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16105 q selected
    | true =>
      simp only [d176467, d177636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176468 q = 0) : d177637 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176468, d177637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176468, d177637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176469 q = 0) : d177638 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176469, d177638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176469, d177638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176470 q = 0) : d177639 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176470, d177639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176470, d177639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176471 q = 0) : d177640 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176471, d177640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176471, d177640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176473 q = 0) : d177642 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176473, d177642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16108 q selected
    | true =>
      simp only [d176473, d177642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176474 q = 0) : d177643 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176474, d177643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176474, d177643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176475 q = 0) : d177644 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176475, d177644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176475, d177644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d176476 q = 0) : d177645 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176476, d177645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176476, d177645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176477 q = 0) : d177646 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176477, d177646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176477, d177646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d176478 q = 0) : d177647 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176478, d177647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176478, d177647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16138 (p : Pattern) (selected : d176485 p = 0) : d177654 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176454 q = 0) : d177626 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176454, d177626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16131 q selected
    | true =>
      simp only [d176454, d177626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16107 q selected
  have h2 (q : Pattern) (selected : d176457 q = 0) : d177556 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176457, d177556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16132 q selected
    | true =>
      simp only [d176457, d177556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16133 q selected
  have h3 (q : Pattern) (selected : d176458 q = 0) : d177627 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176458, d177627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d176458, d177627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176460 q = 0) : d177629 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176460, d177629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16134 q selected
    | true =>
      simp only [d176460, d177629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176461 q = 0) : d177630 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176461, d177630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176461, d177630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176462 q = 0) : d177631 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176462, d177631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176462, d177631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176483 q = 0) : d177652 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176483, d177652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176483, d177652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176484 q = 0) : d177653 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176484, d177653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176484, d177653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d176485 q = 0) : d177654 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176485, d177654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176485, d177654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro16139 (p : Pattern) (selected : d176487 p = 0) : d177656 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176473 q = 0) : d177642 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176473, d177642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16108 q selected
    | true =>
      simp only [d176473, d177642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176474 q = 0) : d177643 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176474, d177643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176474, d177643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176475 q = 0) : d177644 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176475, d177644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176475, d177644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176476 q = 0) : d177645 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176476, d177645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176476, d177645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176477 q = 0) : d177646 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176477, d177646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176477, d177646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176487 q = 0) : d177656 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176487, d177656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176487, d177656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16140 (p : Pattern) (selected : d14990 p = 0) : d123115 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14987 q = 0) : d123112 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14987, d123112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14987, d123112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6670 q selected
  have h2 (q : Pattern) (selected : d9763 q = 0) : d101284 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9763, d101284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6670 q selected
    | true =>
      simp only [d9763, d101284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d14988 q = 0) : d123113 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14988, d123113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d14988, d123113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9765 q = 0) : d101286 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9765, d101286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9765, d101286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14989 q = 0) : d123114 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14989, d123114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14989, d123114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14990 q = 0) : d123115 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14990, d123115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14990, d123115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16141 (p : Pattern) (selected : d14997 p = 0) : d123122 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14994 q = 0) : d123119 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14994, d123119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14994, d123119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6672 q selected
  have h2 (q : Pattern) (selected : d9778 q = 0) : d101299 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9778, d101299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6672 q selected
    | true =>
      simp only [d9778, d101299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d14995 q = 0) : d123120 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14995, d123120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d14995, d123120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9780 q = 0) : d101301 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9780, d101301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9780, d101301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14996 q = 0) : d123121 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14996, d123121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14996, d123121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14997 q = 0) : d123122 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14997, d123122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14997, d123122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16142 (p : Pattern) (selected : d15007 p = 0) : d123132 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d15004 q = 0) : d123129 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15004, d123129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15004, d123129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6675 q selected
  have h2 (q : Pattern) (selected : d9800 q = 0) : d101321 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6675 q selected
    | true =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15005 q = 0) : d123130 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15005, d123130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d15005, d123130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9802 q = 0) : d101323 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9802, d101323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9802, d101323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15006 q = 0) : d123131 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15006, d123131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15006, d123131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15007 q = 0) : d123132 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15007, d123132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15007, d123132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16143 (p : Pattern) (selected : d15022 p = 0) : d123147 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d15019 q = 0) : d123144 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15019, d123144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15019, d123144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6680 q selected
  have h2 (q : Pattern) (selected : d9844 q = 0) : d101365 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6680 q selected
    | true =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15020 q = 0) : d123145 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15020, d123145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d15020, d123145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9846 q = 0) : d101367 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9846, d101367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9846, d101367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15021 q = 0) : d123146 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15021, d123146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15021, d123146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15022 q = 0) : d123147 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15022, d123147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15022, d123147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16144 (p : Pattern) (selected : d176505 p = 0) : d177674 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176493 q = 0) : d177662 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176493, d177662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16140 q selected
    | true =>
      simp only [d176493, d177662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16141 q selected
  have h2 (q : Pattern) (selected : d176494 q = 0) : d177663 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176494, d177663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176494, d177663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176495 q = 0) : d177664 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176495, d177664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176495, d177664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176496 q = 0) : d177665 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176496, d177665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16141 q selected
    | true =>
      simp only [d176496, d177665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16142 q selected
  have h5 (q : Pattern) (selected : d176497 q = 0) : d177666 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176497, d177666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176497, d177666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176498 q = 0) : d177667 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176498, d177667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176498, d177667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176499 q = 0) : d177668 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176499, d177668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176499, d177668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176500 q = 0) : d177669 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176500, d177669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16142 q selected
    | true =>
      simp only [d176500, d177669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16143 q selected
  have h9 (q : Pattern) (selected : d176501 q = 0) : d177670 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176501, d177670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176501, d177670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176502 q = 0) : d177671 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176502, d177671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176502, d177671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d176503 q = 0) : d177672 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176503, d177672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176503, d177672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d176504 q = 0) : d177673 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176504, d177673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176504, d177673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d176505 q = 0) : d177674 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176505, d177674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d176505, d177674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro16145 (p : Pattern) (selected : d176510 p = 0) : d177679 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176496 q = 0) : d177665 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176496, d177665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16141 q selected
    | true =>
      simp only [d176496, d177665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16142 q selected
  have h2 (q : Pattern) (selected : d176497 q = 0) : d177666 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176497, d177666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176497, d177666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176498 q = 0) : d177667 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176498, d177667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176498, d177667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176500 q = 0) : d177669 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176500, d177669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16142 q selected
    | true =>
      simp only [d176500, d177669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16143 q selected
  have h5 (q : Pattern) (selected : d176501 q = 0) : d177670 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176501, d177670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176501, d177670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176502 q = 0) : d177671 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176502, d177671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176502, d177671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176503 q = 0) : d177672 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176503, d177672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176503, d177672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176508 q = 0) : d177677 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176508, d177677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176508, d177677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d176509 q = 0) : d177678 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176509, d177678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176509, d177678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176510 q = 0) : d177679 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176510, d177679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d176510, d177679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16146 (p : Pattern) (selected : d176516 p = 0) : d177685 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176506 q = 0) : d177675 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176506, d177675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16144 q selected
    | true =>
      simp only [d176506, d177675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176507 q = 0) : d177676 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176507, d177676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176507, d177676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176511 q = 0) : d177680 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176511, d177680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16145 q selected
    | true =>
      simp only [d176511, d177680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176512 q = 0) : d177681 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176512, d177681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176512, d177681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176513 q = 0) : d177682 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176513, d177682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176513, d177682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176514 q = 0) : d177683 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176514, d177683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176514, d177683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176515 q = 0) : d177684 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176515, d177684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176515, d177684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176516 q = 0) : d177685 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176516, d177685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176516, d177685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16147 (p : Pattern) (selected : d176518 p = 0) : d177687 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176500 q = 0) : d177669 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176500, d177669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16142 q selected
    | true =>
      simp only [d176500, d177669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16143 q selected
  have h2 (q : Pattern) (selected : d176501 q = 0) : d177670 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176501, d177670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176501, d177670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176502 q = 0) : d177671 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176502, d177671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176502, d177671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176508 q = 0) : d177677 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176508, d177677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176508, d177677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176517 q = 0) : d177686 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176517, d177686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176517, d177686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176518 q = 0) : d177687 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176518, d177687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176518, d177687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16148 (p : Pattern) (selected : d176524 p = 0) : d177693 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176511 q = 0) : d177680 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176511, d177680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16145 q selected
    | true =>
      simp only [d176511, d177680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176512 q = 0) : d177681 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176512, d177681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176512, d177681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176519 q = 0) : d177688 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176519, d177688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16147 q selected
    | true =>
      simp only [d176519, d177688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176520 q = 0) : d177689 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176520, d177689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176520, d177689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176521 q = 0) : d177690 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176521, d177690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176521, d177690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176522 q = 0) : d177691 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176522, d177691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176522, d177691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176523 q = 0) : d177692 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176523, d177692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176523, d177692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176524 q = 0) : d177693 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176524, d177693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176524, d177693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16149 (p : Pattern) (selected : d15060 p = 0) : d123122 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d15057 q = 0) : d123119 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15057, d123119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15057, d123119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6691 q selected
  have h2 (q : Pattern) (selected : d9908 q = 0) : d101299 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9908, d101299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6691 q selected
    | true =>
      simp only [d9908, d101299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15058 q = 0) : d123120 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15058, d123120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d15058, d123120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9910 q = 0) : d101301 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9910, d101301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9910, d101301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15059 q = 0) : d123121 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15059, d123121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15059, d123121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15060 q = 0) : d123122 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15060, d123122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15060, d123122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16150 (p : Pattern) (selected : d15067 p = 0) : d123132 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d15064 q = 0) : d123129 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15064, d123129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15064, d123129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6692 q selected
  have h2 (q : Pattern) (selected : d9918 q = 0) : d101321 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9918, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6692 q selected
    | true =>
      simp only [d9918, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15065 q = 0) : d123130 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15065, d123130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d15065, d123130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9920 q = 0) : d101323 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9920, d101323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9920, d101323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15066 q = 0) : d123131 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15066, d123131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15066, d123131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15067 q = 0) : d123132 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15067, d123132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15067, d123132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16151 (p : Pattern) (selected : d15076 p = 0) : d123147 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d15073 q = 0) : d123144 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15073, d123144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15073, d123144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6696 q selected
  have h2 (q : Pattern) (selected : d9952 q = 0) : d101365 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9952, d101365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6696 q selected
    | true =>
      simp only [d9952, d101365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15074 q = 0) : d123145 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15074, d123145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d15074, d123145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9954 q = 0) : d101367 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9954, d101367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9954, d101367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15075 q = 0) : d123146 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15075, d123146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15075, d123146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15076 q = 0) : d123147 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15076, d123147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15076, d123147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16152 (p : Pattern) (selected : d176535 p = 0) : d177679 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176526 q = 0) : d177665 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176526, d177665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16149 q selected
    | true =>
      simp only [d176526, d177665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16150 q selected
  have h2 (q : Pattern) (selected : d176527 q = 0) : d177666 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176527, d177666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176527, d177666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176528 q = 0) : d177667 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176528, d177667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176528, d177667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176529 q = 0) : d177669 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176529, d177669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16150 q selected
    | true =>
      simp only [d176529, d177669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16151 q selected
  have h5 (q : Pattern) (selected : d176530 q = 0) : d177670 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176530, d177670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176530, d177670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176531 q = 0) : d177671 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176531, d177671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176531, d177671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176532 q = 0) : d177672 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176532, d177672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176532, d177672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176533 q = 0) : d177677 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176533, d177677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176533, d177677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d176534 q = 0) : d177678 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176534, d177678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176534, d177678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176535 q = 0) : d177679 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176535, d177679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d176535, d177679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16153 (p : Pattern) (selected : d176539 p = 0) : d177687 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176529 q = 0) : d177669 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176529, d177669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16150 q selected
    | true =>
      simp only [d176529, d177669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16151 q selected
  have h2 (q : Pattern) (selected : d176530 q = 0) : d177670 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176530, d177670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176530, d177670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176531 q = 0) : d177671 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176531, d177671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176531, d177671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176533 q = 0) : d177677 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176533, d177677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176533, d177677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176538 q = 0) : d177686 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176538, d177686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176538, d177686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176539 q = 0) : d177687 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176539, d177687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176539, d177687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16154 (p : Pattern) (selected : d176545 p = 0) : d177693 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176536 q = 0) : d177680 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176536, d177680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16152 q selected
    | true =>
      simp only [d176536, d177680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176537 q = 0) : d177681 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176537, d177681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176537, d177681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176540 q = 0) : d177688 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176540, d177688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16153 q selected
    | true =>
      simp only [d176540, d177688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176541 q = 0) : d177689 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176541, d177689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176541, d177689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176542 q = 0) : d177690 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176542, d177690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176542, d177690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176543 q = 0) : d177691 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176543, d177691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176543, d177691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176544 q = 0) : d177692 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176544, d177692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176544, d177692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176545 q = 0) : d177693 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176545, d177693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176545, d177693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16155 (p : Pattern) (selected : d176549 p = 0) : d177698 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176540 q = 0) : d177688 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176540, d177688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16153 q selected
    | true =>
      simp only [d176540, d177688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176541 q = 0) : d177689 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176541, d177689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176541, d177689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176546 q = 0) : d177695 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176546, d177695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176546, d177695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176547 q = 0) : d177696 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176547, d177696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176547, d177696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176548 q = 0) : d177697 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176548, d177697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176548, d177697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176549 q = 0) : d177698 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176549, d177698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176549, d177698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16156 (p : Pattern) (selected : d176557 p = 0) : d177706 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176496 q = 0) : d177665 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176496, d177665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16141 q selected
    | true =>
      simp only [d176496, d177665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16142 q selected
  have h2 (q : Pattern) (selected : d176497 q = 0) : d177666 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176497, d177666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176497, d177666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176498 q = 0) : d177667 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176498, d177667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176498, d177667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176500 q = 0) : d177669 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176500, d177669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16142 q selected
    | true =>
      simp only [d176500, d177669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16143 q selected
  have h5 (q : Pattern) (selected : d176501 q = 0) : d177670 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176501, d177670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176501, d177670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176502 q = 0) : d177671 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176502, d177671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176502, d177671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176503 q = 0) : d177672 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176503, d177672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176503, d177672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176552 q = 0) : d177701 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176552, d177701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16142 q selected
    | true =>
      simp only [d176552, d177701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d176553 q = 0) : d177702 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176553, d177702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176553, d177702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176554 q = 0) : d177703 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176554, d177703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176554, d177703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d176555 q = 0) : d177704 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176555, d177704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d176555, d177704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d176556 q = 0) : d177705 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176556, d177705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176556, d177705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d176557 q = 0) : d177706 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176557, d177706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d176557, d177706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro16157 (p : Pattern) (selected : d176563 p = 0) : d177712 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176558 q = 0) : d177707 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176558, d177707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16156 q selected
    | true =>
      simp only [d176558, d177707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176559 q = 0) : d177708 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176559, d177708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176559, d177708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176560 q = 0) : d177709 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176560, d177709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176560, d177709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176561 q = 0) : d177710 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176561, d177710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176561, d177710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176562 q = 0) : d177711 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176562, d177711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176562, d177711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176563 q = 0) : d177712 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176563, d177712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176563, d177712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16158 (p : Pattern) (selected : d176569 p = 0) : d177718 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176525 q = 0) : d177694 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176525, d177694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16146 q selected
    | true =>
      simp only [d176525, d177694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16148 q selected
  have h2 (q : Pattern) (selected : d176550 q = 0) : d177699 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176550, d177699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16154 q selected
    | true =>
      simp only [d176550, d177699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16155 q selected
  have h3 (q : Pattern) (selected : d176551 q = 0) : d177700 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176551, d177700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d176551, d177700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176564 q = 0) : d177713 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176564, d177713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16157 q selected
    | true =>
      simp only [d176564, d177713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176565 q = 0) : d177714 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176565, d177714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176565, d177714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176566 q = 0) : d177715 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176566, d177715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176566, d177715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176567 q = 0) : d177716 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176567, d177716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176567, d177716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176568 q = 0) : d177717 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176568, d177717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176568, d177717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d176569 q = 0) : d177718 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176569, d177718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176569, d177718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro16159 (p : Pattern) (selected : d176574 p = 0) : d177698 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176519 q = 0) : d177688 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176519, d177688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16147 q selected
    | true =>
      simp only [d176519, d177688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176520 q = 0) : d177689 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176520, d177689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176520, d177689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176571 q = 0) : d177695 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176571, d177695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176571, d177695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176572 q = 0) : d177696 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176572, d177696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176572, d177696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176573 q = 0) : d177697 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176573, d177697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176573, d177697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176574 q = 0) : d177698 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176574, d177698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176574, d177698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16160 (p : Pattern) (selected : d176580 p = 0) : d177725 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176575 q = 0) : d177720 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176575, d177720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16159 q selected
    | true =>
      simp only [d176575, d177720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176576 q = 0) : d177721 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176576, d177721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176576, d177721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176577 q = 0) : d177722 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176577, d177722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176577, d177722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176578 q = 0) : d177723 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176578, d177723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176578, d177723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176579 q = 0) : d177724 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176579, d177724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176579, d177724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176580 q = 0) : d177725 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176580, d177725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176580, d177725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16161 (p : Pattern) (selected : d176586 p = 0) : d177731 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176355 q = 0) : d177552 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d176355, d177552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176355, d177552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16106 q selected
  have h2 (q : Pattern) (selected : d176356 q = 0) : d177553 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d176356, d177553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d176356, d177553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d176365 q = 0) : d177562 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d176365, d177562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16106 q selected
    | true =>
      simp only [d176365, d177562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16109 q selected
  have h4 (q : Pattern) (selected : d176366 q = 0) : d177563 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d176366, d177563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176366, d177563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176367 q = 0) : d177564 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d176367, d177564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176367, d177564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176466 q = 0) : d177635 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d176466, d177635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16126 q selected
    | true =>
      simp only [d176466, d177635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16135 q selected
  have h7 (q : Pattern) (selected : d176479 q = 0) : d177648 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d176479, d177648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16136 q selected
    | true =>
      simp only [d176479, d177648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16137 q selected
  have h8 (q : Pattern) (selected : d176480 q = 0) : d177649 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d176480, d177649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176480, d177649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d176481 q = 0) : d177650 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d176481, d177650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d176481, d177650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d176482 q = 0) : d177651 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d176482, d177651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176482, d177651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d176486 q = 0) : d177655 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d176486, d177655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176486, d177655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16138 q selected
  have h12 (q : Pattern) (selected : d176488 q = 0) : d177657 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d176488, d177657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176488, d177657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16139 q selected
  have h13 (q : Pattern) (selected : d176489 q = 0) : d177658 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d176489, d177658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d176489, d177658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d176490 q = 0) : d177659 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d176490, d177659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d176490, d177659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d176491 q = 0) : d177660 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d176491, d177660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d176491, d177660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d176492 q = 0) : d177661 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d176492, d177661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d176492, d177661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d176570 q = 0) : d177719 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d176570, d177719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176570, d177719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16158 q selected
  have h18 (q : Pattern) (selected : d176581 q = 0) : d177726 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d176581, d177726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176581, d177726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16160 q selected
  have h19 (q : Pattern) (selected : d176582 q = 0) : d177727 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d176582, d177727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d176582, d177727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d176583 q = 0) : d177728 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d176583, d177728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d176583, d177728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d176584 q = 0) : d177729 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d176584, d177729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d176584, d177729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d176585 q = 0) : d177730 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d176585, d177730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d176585, d177730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d176586 q = 0) : d177731 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d176586, d177731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d176586, d177731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro16162 (p : Pattern) (selected : d176592 p = 0) : d177737 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176587 q = 0) : d177732 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d176587, d177732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176587, d177732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16161 q selected
  have h2 (q : Pattern) (selected : d176588 q = 0) : d177733 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d176588, d177733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176588, d177733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176589 q = 0) : d177734 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d176589, d177734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176589, d177734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176590 q = 0) : d177735 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d176590, d177735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176590, d177735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176591 q = 0) : d177736 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d176591, d177736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176591, d177736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176592 q = 0) : d177737 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d176592, d177737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176592, d177737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16163 (p : Pattern) (selected : d15152 p = 0) : d123237 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10063 q = 0) : d101490 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10063, d101490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6714 q selected
    | true =>
      simp only [d10063, d101490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10065 q = 0) : d101492 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10065, d101492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10065, d101492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15151 q = 0) : d123236 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15151, d123236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15151, d123236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d15152 q = 0) : d123237 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15152, d123237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15152, d123237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16164 (p : Pattern) (selected : d15157 p = 0) : d123242 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10085 q = 0) : d101512 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6717 q selected
    | true =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10087 q = 0) : d101514 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10087, d101514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10087, d101514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15156 q = 0) : d123241 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15156, d123241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15156, d123241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d15157 q = 0) : d123242 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15157, d123242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15157, d123242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16165 (p : Pattern) (selected : d15164 p = 0) : d123249 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10135 q = 0) : d101562 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6723 q selected
    | true =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10137 q = 0) : d101564 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10137, d101564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10137, d101564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15163 q = 0) : d123248 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15163, d123248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15163, d123248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d15164 q = 0) : d123249 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15164, d123249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15164, d123249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16166 (p : Pattern) (selected : d176605 p = 0) : d177750 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176596 q = 0) : d177741 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176596, d177741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16163 q selected
    | true =>
      simp only [d176596, d177741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16164 q selected
  have h2 (q : Pattern) (selected : d176597 q = 0) : d177742 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176597, d177742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176597, d177742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176598 q = 0) : d177743 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176598, d177743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176598, d177743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176599 q = 0) : d177744 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176599, d177744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16164 q selected
    | true =>
      simp only [d176599, d177744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16165 q selected
  have h5 (q : Pattern) (selected : d176600 q = 0) : d177745 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176600, d177745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176600, d177745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176601 q = 0) : d177746 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176601, d177746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176601, d177746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176602 q = 0) : d177747 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176602, d177747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176602, d177747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176603 q = 0) : d177748 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176603, d177748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176603, d177748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d176604 q = 0) : d177749 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176604, d177749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176604, d177749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176605 q = 0) : d177750 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176605, d177750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d176605, d177750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16167 (p : Pattern) (selected : d176609 p = 0) : d177754 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176599 q = 0) : d177744 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176599, d177744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16164 q selected
    | true =>
      simp only [d176599, d177744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16165 q selected
  have h2 (q : Pattern) (selected : d176600 q = 0) : d177745 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176600, d177745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176600, d177745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176601 q = 0) : d177746 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176601, d177746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176601, d177746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176603 q = 0) : d177748 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176603, d177748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176603, d177748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176608 q = 0) : d177753 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176608, d177753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176608, d177753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176609 q = 0) : d177754 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176609, d177754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176609, d177754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16168 (p : Pattern) (selected : d176615 p = 0) : d177760 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176606 q = 0) : d177751 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176606, d177751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16166 q selected
    | true =>
      simp only [d176606, d177751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176607 q = 0) : d177752 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176607, d177752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176607, d177752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176610 q = 0) : d177755 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176610, d177755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16167 q selected
    | true =>
      simp only [d176610, d177755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176611 q = 0) : d177756 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176611, d177756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176611, d177756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176612 q = 0) : d177757 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176612, d177757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176612, d177757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176613 q = 0) : d177758 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176613, d177758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176613, d177758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176614 q = 0) : d177759 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176614, d177759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176614, d177759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176615 q = 0) : d177760 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176615, d177760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176615, d177760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16169 (p : Pattern) (selected : d176619 p = 0) : d177764 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176610 q = 0) : d177755 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176610, d177755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16167 q selected
    | true =>
      simp only [d176610, d177755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176611 q = 0) : d177756 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176611, d177756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176611, d177756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176616 q = 0) : d177761 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176616, d177761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176616, d177761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176617 q = 0) : d177762 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176617, d177762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176617, d177762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176618 q = 0) : d177763 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176618, d177763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176618, d177763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176619 q = 0) : d177764 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176619, d177764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176619, d177764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16170 (p : Pattern) (selected : d176625 p = 0) : d177770 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176620 q = 0) : d177765 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176620, d177765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16168 q selected
    | true =>
      simp only [d176620, d177765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16169 q selected
  have h2 (q : Pattern) (selected : d176621 q = 0) : d177766 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176621, d177766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176621, d177766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176622 q = 0) : d177767 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176622, d177767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176622, d177767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176623 q = 0) : d177768 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176623, d177768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176623, d177768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176624 q = 0) : d177769 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176624, d177769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176624, d177769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176625 q = 0) : d177770 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176625, d177770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176625, d177770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16171 (p : Pattern) (selected : d176628 p = 0) : d177773 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176606 q = 0) : d177751 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176606, d177751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16166 q selected
    | true =>
      simp only [d176606, d177751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176607 q = 0) : d177752 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176607, d177752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176607, d177752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176610 q = 0) : d177755 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176610, d177755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16167 q selected
    | true =>
      simp only [d176610, d177755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176611 q = 0) : d177756 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176611, d177756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176611, d177756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176612 q = 0) : d177757 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176612, d177757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176612, d177757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176613 q = 0) : d177758 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176613, d177758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176613, d177758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176614 q = 0) : d177759 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176614, d177759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176614, d177759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176628 q = 0) : d177773 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176628, d177773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176628, d177773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16172 (p : Pattern) (selected : d176629 p = 0) : d177774 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176610 q = 0) : d177755 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176610, d177755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16167 q selected
    | true =>
      simp only [d176610, d177755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176611 q = 0) : d177756 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176611, d177756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176611, d177756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176616 q = 0) : d177761 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176616, d177761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176616, d177761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176617 q = 0) : d177762 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176617, d177762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176617, d177762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176618 q = 0) : d177763 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176618, d177763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176618, d177763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176629 q = 0) : d177774 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176629, d177774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176629, d177774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16173 (p : Pattern) (selected : d176635 p = 0) : d177780 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176620 q = 0) : d177765 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176620, d177765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16168 q selected
    | true =>
      simp only [d176620, d177765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16169 q selected
  have h2 (q : Pattern) (selected : d176621 q = 0) : d177766 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176621, d177766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176621, d177766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176622 q = 0) : d177767 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176622, d177767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176622, d177767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176623 q = 0) : d177768 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176623, d177768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176623, d177768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176624 q = 0) : d177769 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176624, d177769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176624, d177769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176630 q = 0) : d177775 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176630, d177775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16171 q selected
    | true =>
      simp only [d176630, d177775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16172 q selected
  have h7 (q : Pattern) (selected : d176631 q = 0) : d177776 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176631, d177776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176631, d177776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176632 q = 0) : d177777 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176632, d177777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176632, d177777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d176633 q = 0) : d177778 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176633, d177778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176633, d177778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176634 q = 0) : d177779 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176634, d177779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176634, d177779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d176635 q = 0) : d177780 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176635, d177780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176635, d177780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16174 (p : Pattern) (selected : d176640 p = 0) : d177785 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176606 q = 0) : d177751 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176606, d177751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16166 q selected
    | true =>
      simp only [d176606, d177751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176607 q = 0) : d177752 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176607, d177752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176607, d177752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176610 q = 0) : d177755 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176610, d177755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16167 q selected
    | true =>
      simp only [d176610, d177755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176611 q = 0) : d177756 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176611, d177756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176611, d177756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176612 q = 0) : d177757 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176612, d177757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176612, d177757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176613 q = 0) : d177758 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176613, d177758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176613, d177758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176639 q = 0) : d177784 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176639, d177784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176639, d177784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176640 q = 0) : d177785 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176640, d177785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176640, d177785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16175 (p : Pattern) (selected : d176642 p = 0) : d177787 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176610 q = 0) : d177755 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176610, d177755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16167 q selected
    | true =>
      simp only [d176610, d177755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176611 q = 0) : d177756 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176611, d177756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176611, d177756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176616 q = 0) : d177761 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176616, d177761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176616, d177761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176617 q = 0) : d177762 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176617, d177762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176617, d177762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176641 q = 0) : d177786 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176641, d177786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176641, d177786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176642 q = 0) : d177787 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176642, d177787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176642, d177787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16176 (p : Pattern) (selected : d176649 p = 0) : d177794 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176606 q = 0) : d177751 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176606, d177751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16166 q selected
    | true =>
      simp only [d176606, d177751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176607 q = 0) : d177752 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176607, d177752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176607, d177752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176610 q = 0) : d177755 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176610, d177755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16167 q selected
    | true =>
      simp only [d176610, d177755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176611 q = 0) : d177756 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176611, d177756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176611, d177756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176612 q = 0) : d177757 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176612, d177757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176612, d177757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176647 q = 0) : d177792 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176647, d177792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176647, d177792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176648 q = 0) : d177793 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176648, d177793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176648, d177793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176649 q = 0) : d177794 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176649, d177794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176649, d177794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16177 (p : Pattern) (selected : d176652 p = 0) : d177797 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176610 q = 0) : d177755 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176610, d177755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16167 q selected
    | true =>
      simp only [d176610, d177755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176611 q = 0) : d177756 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176611, d177756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176611, d177756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176616 q = 0) : d177761 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176616, d177761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176616, d177761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176650 q = 0) : d177795 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176650, d177795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176650, d177795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176651 q = 0) : d177796 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176651, d177796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176651, d177796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176652 q = 0) : d177797 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176652, d177797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176652, d177797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16178 (p : Pattern) (selected : d15230 p = 0) : d123315 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10046 q = 0) : d101473 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10046, d101473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6712 q selected
    | true =>
      simp only [d10046, d101473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10048 q = 0) : d101475 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10048, d101475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10048, d101475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15229 q = 0) : d123314 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15229, d123314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15229, d123314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d15230 q = 0) : d123315 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15230, d123315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15230, d123315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16179 (p : Pattern) (selected : d176661 p = 0) : d177806 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176656 q = 0) : d177801 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176656, d177801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16178 q selected
    | true =>
      simp only [d176656, d177801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16163 q selected
  have h2 (q : Pattern) (selected : d176657 q = 0) : d177802 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176657, d177802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176657, d177802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176658 q = 0) : d177803 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176658, d177803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176658, d177803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176596 q = 0) : d177741 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176596, d177741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16163 q selected
    | true =>
      simp only [d176596, d177741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16164 q selected
  have h5 (q : Pattern) (selected : d176597 q = 0) : d177742 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176597, d177742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176597, d177742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176598 q = 0) : d177743 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176598, d177743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176598, d177743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176659 q = 0) : d177804 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176659, d177804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176659, d177804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176599 q = 0) : d177744 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176599, d177744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16164 q selected
    | true =>
      simp only [d176599, d177744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16165 q selected
  have h9 (q : Pattern) (selected : d176600 q = 0) : d177745 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176600, d177745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176600, d177745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176601 q = 0) : d177746 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176601, d177746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176601, d177746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d176602 q = 0) : d177747 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176602, d177747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176602, d177747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d176660 q = 0) : d177805 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176660, d177805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176660, d177805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d176661 q = 0) : d177806 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176661, d177806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d176661, d177806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro16180 (p : Pattern) (selected : d176667 p = 0) : d177812 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176662 q = 0) : d177807 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176662, d177807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16179 q selected
    | true =>
      simp only [d176662, d177807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176663 q = 0) : d177808 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176663, d177808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176663, d177808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176606 q = 0) : d177751 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176606, d177751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16166 q selected
    | true =>
      simp only [d176606, d177751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176607 q = 0) : d177752 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176607, d177752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176607, d177752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176664 q = 0) : d177809 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176664, d177809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176664, d177809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176665 q = 0) : d177810 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176665, d177810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176665, d177810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176666 q = 0) : d177811 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176666, d177811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176666, d177811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176667 q = 0) : d177812 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176667, d177812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176667, d177812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16181 (p : Pattern) (selected : d15262 p = 0) : d123237 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10200 q = 0) : d101490 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10200, d101490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6734 q selected
    | true =>
      simp only [d10200, d101490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10202 q = 0) : d101492 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10202, d101492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10202, d101492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15261 q = 0) : d123236 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15261, d123236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15261, d123236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d15262 q = 0) : d123237 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15262, d123237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15262, d123237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16182 (p : Pattern) (selected : d15267 p = 0) : d123242 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10215 q = 0) : d101512 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10215, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6735 q selected
    | true =>
      simp only [d10215, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10217 q = 0) : d101514 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10217, d101514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10217, d101514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15266 q = 0) : d123241 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15266, d123241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15266, d123241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d15267 q = 0) : d123242 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15267, d123242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15267, d123242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16183 (p : Pattern) (selected : d15274 p = 0) : d123249 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10255 q = 0) : d101562 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10255, d101562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6740 q selected
    | true =>
      simp only [d10255, d101562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10257 q = 0) : d101564 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10257, d101564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10257, d101564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15273 q = 0) : d123248 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15273, d123248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15273, d123248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d15274 q = 0) : d123249 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15274, d123249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15274, d123249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16184 (p : Pattern) (selected : d176678 p = 0) : d177750 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176669 q = 0) : d177741 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176669, d177741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16181 q selected
    | true =>
      simp only [d176669, d177741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16182 q selected
  have h2 (q : Pattern) (selected : d176670 q = 0) : d177742 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176670, d177742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176670, d177742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176671 q = 0) : d177743 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176671, d177743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176671, d177743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176672 q = 0) : d177744 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176672, d177744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16182 q selected
    | true =>
      simp only [d176672, d177744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16183 q selected
  have h5 (q : Pattern) (selected : d176673 q = 0) : d177745 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176673, d177745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176673, d177745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176674 q = 0) : d177746 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176674, d177746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176674, d177746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176675 q = 0) : d177747 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176675, d177747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176675, d177747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176676 q = 0) : d177748 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176676, d177748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176676, d177748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d176677 q = 0) : d177749 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176677, d177749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176677, d177749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176678 q = 0) : d177750 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176678, d177750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d176678, d177750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16185 (p : Pattern) (selected : d176682 p = 0) : d177754 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176672 q = 0) : d177744 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176672, d177744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16182 q selected
    | true =>
      simp only [d176672, d177744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16183 q selected
  have h2 (q : Pattern) (selected : d176673 q = 0) : d177745 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176673, d177745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176673, d177745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176674 q = 0) : d177746 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176674, d177746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176674, d177746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176676 q = 0) : d177748 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176676, d177748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176676, d177748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176681 q = 0) : d177753 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176681, d177753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176681, d177753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176682 q = 0) : d177754 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176682, d177754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176682, d177754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16186 (p : Pattern) (selected : d176688 p = 0) : d177760 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176679 q = 0) : d177751 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176679, d177751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16184 q selected
    | true =>
      simp only [d176679, d177751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176680 q = 0) : d177752 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176680, d177752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176680, d177752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176683 q = 0) : d177755 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176683, d177755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16185 q selected
    | true =>
      simp only [d176683, d177755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176684 q = 0) : d177756 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176684, d177756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176684, d177756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176685 q = 0) : d177757 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176685, d177757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176685, d177757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176686 q = 0) : d177758 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176686, d177758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176686, d177758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176687 q = 0) : d177759 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176687, d177759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176687, d177759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176688 q = 0) : d177760 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176688, d177760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176688, d177760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16187 (p : Pattern) (selected : d176692 p = 0) : d177764 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176683 q = 0) : d177755 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176683, d177755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16185 q selected
    | true =>
      simp only [d176683, d177755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176684 q = 0) : d177756 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176684, d177756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176684, d177756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176689 q = 0) : d177761 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176689, d177761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176689, d177761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176690 q = 0) : d177762 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176690, d177762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176690, d177762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176691 q = 0) : d177763 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176691, d177763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176691, d177763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176692 q = 0) : d177764 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176692, d177764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176692, d177764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16188 (p : Pattern) (selected : d176700 p = 0) : d177820 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176596 q = 0) : d177741 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176596, d177741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16163 q selected
    | true =>
      simp only [d176596, d177741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16164 q selected
  have h2 (q : Pattern) (selected : d176597 q = 0) : d177742 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176597, d177742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176597, d177742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176598 q = 0) : d177743 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176598, d177743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176598, d177743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176599 q = 0) : d177744 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176599, d177744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16164 q selected
    | true =>
      simp only [d176599, d177744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16165 q selected
  have h5 (q : Pattern) (selected : d176600 q = 0) : d177745 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176600, d177745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176600, d177745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176601 q = 0) : d177746 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176601, d177746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176601, d177746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176602 q = 0) : d177747 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176602, d177747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176602, d177747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176695 q = 0) : d177815 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176695, d177815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16164 q selected
    | true =>
      simp only [d176695, d177815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d176696 q = 0) : d177816 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176696, d177816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176696, d177816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176697 q = 0) : d177817 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176697, d177817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176697, d177817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d176698 q = 0) : d177818 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176698, d177818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d176698, d177818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d176699 q = 0) : d177819 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176699, d177819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176699, d177819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d176700 q = 0) : d177820 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176700, d177820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d176700, d177820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro16189 (p : Pattern) (selected : d176706 p = 0) : d177826 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176701 q = 0) : d177821 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176701, d177821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16188 q selected
    | true =>
      simp only [d176701, d177821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176702 q = 0) : d177822 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176702, d177822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176702, d177822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176703 q = 0) : d177823 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176703, d177823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176703, d177823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176704 q = 0) : d177824 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176704, d177824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176704, d177824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176705 q = 0) : d177825 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176705, d177825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176705, d177825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176706 q = 0) : d177826 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176706, d177826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176706, d177826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16190 (p : Pattern) (selected : d176712 p = 0) : d177832 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176643 q = 0) : d177788 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176643, d177788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16174 q selected
    | true =>
      simp only [d176643, d177788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16175 q selected
  have h2 (q : Pattern) (selected : d176644 q = 0) : d177789 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176644, d177789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176644, d177789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176645 q = 0) : d177790 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176645, d177790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176645, d177790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176646 q = 0) : d177791 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176646, d177791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176646, d177791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176653 q = 0) : d177798 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176653, d177798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16176 q selected
    | true =>
      simp only [d176653, d177798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16177 q selected
  have h6 (q : Pattern) (selected : d176654 q = 0) : d177799 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176654, d177799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176654, d177799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176655 q = 0) : d177800 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176655, d177800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176655, d177800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176668 q = 0) : d177813 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176668, d177813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16180 q selected
    | true =>
      simp only [d176668, d177813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16168 q selected
  have h9 (q : Pattern) (selected : d176693 q = 0) : d177765 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176693, d177765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16186 q selected
    | true =>
      simp only [d176693, d177765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16187 q selected
  have h10 (q : Pattern) (selected : d176694 q = 0) : d177814 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176694, d177814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d176694, d177814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d176707 q = 0) : d177827 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176707, d177827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16189 q selected
    | true =>
      simp only [d176707, d177827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d176708 q = 0) : d177828 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176708, d177828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d176708, d177828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d176709 q = 0) : d177829 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176709, d177829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d176709, d177829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d176710 q = 0) : d177830 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176710, d177830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176710, d177830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d176711 q = 0) : d177831 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176711, d177831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176711, d177831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d176712 q = 0) : d177832 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176712, d177832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176712, d177832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro16191 (p : Pattern) (selected : d176713 p = 0) : d177833 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176606 q = 0) : d177751 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176606, d177751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16166 q selected
    | true =>
      simp only [d176606, d177751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176607 q = 0) : d177752 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176607, d177752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176607, d177752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176610 q = 0) : d177755 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176610, d177755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16167 q selected
    | true =>
      simp only [d176610, d177755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176611 q = 0) : d177756 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176611, d177756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176611, d177756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176612 q = 0) : d177757 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176612, d177757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176612, d177757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176613 q = 0) : d177758 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176613, d177758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176613, d177758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176639 q = 0) : d177784 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176639, d177784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176639, d177784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176713 q = 0) : d177833 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176713, d177833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176713, d177833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16192 (p : Pattern) (selected : d176714 p = 0) : d177834 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176610 q = 0) : d177755 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176610, d177755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16167 q selected
    | true =>
      simp only [d176610, d177755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176611 q = 0) : d177756 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176611, d177756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176611, d177756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176616 q = 0) : d177761 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176616, d177761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176616, d177761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176617 q = 0) : d177762 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176617, d177762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176617, d177762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176641 q = 0) : d177786 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176641, d177786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176641, d177786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176714 q = 0) : d177834 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176714, d177834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176714, d177834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16193 (p : Pattern) (selected : d176719 p = 0) : d177839 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176606 q = 0) : d177751 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176606, d177751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16166 q selected
    | true =>
      simp only [d176606, d177751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176607 q = 0) : d177752 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176607, d177752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176607, d177752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176610 q = 0) : d177755 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176610, d177755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16167 q selected
    | true =>
      simp only [d176610, d177755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176611 q = 0) : d177756 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176611, d177756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176611, d177756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176612 q = 0) : d177757 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176612, d177757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176612, d177757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176647 q = 0) : d177792 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176647, d177792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176647, d177792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176648 q = 0) : d177793 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176648, d177793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176648, d177793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176719 q = 0) : d177839 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176719, d177839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176719, d177839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16194 (p : Pattern) (selected : d176720 p = 0) : d177840 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176610 q = 0) : d177755 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176610, d177755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16167 q selected
    | true =>
      simp only [d176610, d177755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176611 q = 0) : d177756 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176611, d177756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176611, d177756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176616 q = 0) : d177761 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176616, d177761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176616, d177761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176650 q = 0) : d177795 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176650, d177795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176650, d177795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176651 q = 0) : d177796 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176651, d177796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176651, d177796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176720 q = 0) : d177840 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176720, d177840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176720, d177840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16195 (p : Pattern) (selected : d176724 p = 0) : d177844 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176662 q = 0) : d177807 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176662, d177807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16179 q selected
    | true =>
      simp only [d176662, d177807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176663 q = 0) : d177808 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176663, d177808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176663, d177808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176606 q = 0) : d177751 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176606, d177751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16166 q selected
    | true =>
      simp only [d176606, d177751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176607 q = 0) : d177752 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176607, d177752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176607, d177752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176664 q = 0) : d177809 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176664, d177809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176664, d177809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176665 q = 0) : d177810 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176665, d177810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176665, d177810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176666 q = 0) : d177811 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176666, d177811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176666, d177811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176724 q = 0) : d177844 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176724, d177844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176724, d177844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16196 (p : Pattern) (selected : d176726 p = 0) : d177773 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176679 q = 0) : d177751 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176679, d177751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16184 q selected
    | true =>
      simp only [d176679, d177751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176680 q = 0) : d177752 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176680, d177752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176680, d177752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176683 q = 0) : d177755 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176683, d177755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16185 q selected
    | true =>
      simp only [d176683, d177755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176684 q = 0) : d177756 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176684, d177756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176684, d177756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176685 q = 0) : d177757 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176685, d177757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176685, d177757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176686 q = 0) : d177758 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176686, d177758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176686, d177758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176687 q = 0) : d177759 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176687, d177759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176687, d177759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176726 q = 0) : d177773 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176726, d177773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176726, d177773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16197 (p : Pattern) (selected : d176727 p = 0) : d177774 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176683 q = 0) : d177755 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176683, d177755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16185 q selected
    | true =>
      simp only [d176683, d177755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176684 q = 0) : d177756 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176684, d177756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176684, d177756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176689 q = 0) : d177761 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176689, d177761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176689, d177761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176690 q = 0) : d177762 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176690, d177762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176690, d177762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176691 q = 0) : d177763 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176691, d177763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176691, d177763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176727 q = 0) : d177774 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176727, d177774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176727, d177774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16198 (p : Pattern) (selected : d176730 p = 0) : d177847 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176701 q = 0) : d177821 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176701, d177821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16188 q selected
    | true =>
      simp only [d176701, d177821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176702 q = 0) : d177822 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176702, d177822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176702, d177822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176703 q = 0) : d177823 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176703, d177823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176703, d177823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176704 q = 0) : d177824 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176704, d177824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176704, d177824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176705 q = 0) : d177825 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176705, d177825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176705, d177825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176730 q = 0) : d177847 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176730, d177847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176730, d177847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16199 (p : Pattern) (selected : d176736 p = 0) : d177853 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176643 q = 0) : d177788 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176643, d177788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16174 q selected
    | true =>
      simp only [d176643, d177788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16175 q selected
  have h2 (q : Pattern) (selected : d176644 q = 0) : d177789 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176644, d177789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176644, d177789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176645 q = 0) : d177790 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176645, d177790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176645, d177790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176646 q = 0) : d177791 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176646, d177791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176646, d177791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176653 q = 0) : d177798 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176653, d177798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16176 q selected
    | true =>
      simp only [d176653, d177798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16177 q selected
  have h6 (q : Pattern) (selected : d176654 q = 0) : d177799 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176654, d177799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176654, d177799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176655 q = 0) : d177800 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176655, d177800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176655, d177800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176668 q = 0) : d177813 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176668, d177813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16180 q selected
    | true =>
      simp only [d176668, d177813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16168 q selected
  have h9 (q : Pattern) (selected : d176693 q = 0) : d177765 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176693, d177765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16186 q selected
    | true =>
      simp only [d176693, d177765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16187 q selected
  have h10 (q : Pattern) (selected : d176694 q = 0) : d177814 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176694, d177814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d176694, d177814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d176707 q = 0) : d177827 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176707, d177827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16189 q selected
    | true =>
      simp only [d176707, d177827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d176708 q = 0) : d177828 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176708, d177828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d176708, d177828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d176709 q = 0) : d177829 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176709, d177829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d176709, d177829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d176710 q = 0) : d177830 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176710, d177830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176710, d177830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d176711 q = 0) : d177831 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176711, d177831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176711, d177831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d176715 q = 0) : d177835 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176715, d177835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16191 q selected
    | true =>
      simp only [d176715, d177835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16192 q selected
  have h17 (q : Pattern) (selected : d176716 q = 0) : d177836 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176716, d177836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176716, d177836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d176717 q = 0) : d177837 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176717, d177837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d176717, d177837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d176718 q = 0) : d177838 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176718, d177838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176718, d177838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d176721 q = 0) : d177841 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176721, d177841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16193 q selected
    | true =>
      simp only [d176721, d177841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16194 q selected
  have h21 (q : Pattern) (selected : d176722 q = 0) : d177842 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176722, d177842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176722, d177842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d176723 q = 0) : d177843 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176723, d177843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d176723, d177843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d176725 q = 0) : d177845 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176725, d177845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16195 q selected
    | true =>
      simp only [d176725, d177845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16171 q selected
  have h24 (q : Pattern) (selected : d176728 q = 0) : d177775 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176728, d177775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16196 q selected
    | true =>
      simp only [d176728, d177775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16197 q selected
  have h25 (q : Pattern) (selected : d176729 q = 0) : d177846 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176729, d177846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d176729, d177846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d176731 q = 0) : d177848 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176731, d177848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16198 q selected
    | true =>
      simp only [d176731, d177848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d176732 q = 0) : d177849 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176732, d177849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d176732, d177849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d176733 q = 0) : d177850 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176733, d177850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d176733, d177850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d176734 q = 0) : d177851 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176734, d177851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d176734, d177851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d176735 q = 0) : d177852 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176735, d177852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d176735, d177852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d176736 q = 0) : d177853 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176736, d177853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d176736, d177853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro16200 (p : Pattern) (selected : d176743 p = 0) : d177860 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176620 q = 0) : d177765 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176620, d177765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16168 q selected
    | true =>
      simp only [d176620, d177765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16169 q selected
  have h2 (q : Pattern) (selected : d176621 q = 0) : d177766 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176621, d177766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176621, d177766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176622 q = 0) : d177767 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176622, d177767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176622, d177767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176623 q = 0) : d177768 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176623, d177768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176623, d177768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176624 q = 0) : d177769 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176624, d177769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176624, d177769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176738 q = 0) : d177855 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176738, d177855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16169 q selected
    | true =>
      simp only [d176738, d177855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176739 q = 0) : d177856 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176739, d177856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176739, d177856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176740 q = 0) : d177857 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176740, d177857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176740, d177857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d176741 q = 0) : d177858 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176741, d177858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176741, d177858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176742 q = 0) : d177859 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176742, d177859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176742, d177859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d176743 q = 0) : d177860 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176743, d177860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176743, d177860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16201 (p : Pattern) (selected : d176749 p = 0) : d177866 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176738 q = 0) : d177855 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176738, d177855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16169 q selected
    | true =>
      simp only [d176738, d177855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176739 q = 0) : d177856 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176739, d177856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176739, d177856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176740 q = 0) : d177857 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176740, d177857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176740, d177857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176741 q = 0) : d177858 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176741, d177858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176741, d177858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176742 q = 0) : d177859 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176742, d177859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176742, d177859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176744 q = 0) : d177861 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176744, d177861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16172 q selected
    | true =>
      simp only [d176744, d177861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176745 q = 0) : d177862 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176745, d177862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176745, d177862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176746 q = 0) : d177863 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176746, d177863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176746, d177863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d176747 q = 0) : d177864 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176747, d177864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176747, d177864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176748 q = 0) : d177865 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176748, d177865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176748, d177865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d176749 q = 0) : d177866 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176749, d177866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176749, d177866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16202 (p : Pattern) (selected : d176756 p = 0) : d177873 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176725 q = 0) : d177845 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176725, d177845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16195 q selected
    | true =>
      simp only [d176725, d177845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16171 q selected
  have h2 (q : Pattern) (selected : d176728 q = 0) : d177775 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176728, d177775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16196 q selected
    | true =>
      simp only [d176728, d177775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16197 q selected
  have h3 (q : Pattern) (selected : d176729 q = 0) : d177846 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176729, d177846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d176729, d177846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176731 q = 0) : d177848 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176731, d177848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16198 q selected
    | true =>
      simp only [d176731, d177848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176732 q = 0) : d177849 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176732, d177849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176732, d177849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176733 q = 0) : d177850 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176733, d177850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176733, d177850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176754 q = 0) : d177871 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176754, d177871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176754, d177871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176755 q = 0) : d177872 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176755, d177872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176755, d177872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d176756 q = 0) : d177873 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176756, d177873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176756, d177873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro16203 (p : Pattern) (selected : d176758 p = 0) : d177875 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176744 q = 0) : d177861 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176744, d177861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16172 q selected
    | true =>
      simp only [d176744, d177861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176745 q = 0) : d177862 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176745, d177862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176745, d177862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176746 q = 0) : d177863 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176746, d177863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176746, d177863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176747 q = 0) : d177864 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176747, d177864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176747, d177864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176748 q = 0) : d177865 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176748, d177865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176748, d177865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176758 q = 0) : d177875 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176758, d177875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176758, d177875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16204 (p : Pattern) (selected : d15383 p = 0) : d123422 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d15380 q = 0) : d123419 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15380, d123419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15380, d123419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6712 q selected
  have h2 (q : Pattern) (selected : d10046 q = 0) : d101473 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10046, d101473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6712 q selected
    | true =>
      simp only [d10046, d101473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15381 q = 0) : d123420 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15381, d123420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d15381, d123420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10048 q = 0) : d101475 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10048, d101475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10048, d101475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15382 q = 0) : d123421 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15382, d123421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15382, d123421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15383 q = 0) : d123422 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15383, d123422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15383, d123422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16205 (p : Pattern) (selected : d15390 p = 0) : d123429 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d15387 q = 0) : d123426 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15387, d123426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15387, d123426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6714 q selected
  have h2 (q : Pattern) (selected : d10063 q = 0) : d101490 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10063, d101490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6714 q selected
    | true =>
      simp only [d10063, d101490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15388 q = 0) : d123427 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15388, d123427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d15388, d123427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10065 q = 0) : d101492 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10065, d101492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10065, d101492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15389 q = 0) : d123428 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15389, d123428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15389, d123428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15390 q = 0) : d123429 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15390, d123429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15390, d123429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16206 (p : Pattern) (selected : d15400 p = 0) : d123439 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d15397 q = 0) : d123436 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15397, d123436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15397, d123436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6717 q selected
  have h2 (q : Pattern) (selected : d10085 q = 0) : d101512 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6717 q selected
    | true =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15398 q = 0) : d123437 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15398, d123437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d15398, d123437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10087 q = 0) : d101514 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10087, d101514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10087, d101514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15399 q = 0) : d123438 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15399, d123438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15399, d123438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15400 q = 0) : d123439 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15400, d123439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15400, d123439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16207 (p : Pattern) (selected : d15415 p = 0) : d123454 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d15412 q = 0) : d123451 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15412, d123451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15412, d123451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6723 q selected
  have h2 (q : Pattern) (selected : d10135 q = 0) : d101562 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6723 q selected
    | true =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15413 q = 0) : d123452 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15413, d123452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d15413, d123452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10137 q = 0) : d101564 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10137, d101564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10137, d101564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15414 q = 0) : d123453 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15414, d123453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15414, d123453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15415 q = 0) : d123454 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15415, d123454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15415, d123454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16208 (p : Pattern) (selected : d176776 p = 0) : d177893 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176764 q = 0) : d177881 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176764, d177881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16204 q selected
    | true =>
      simp only [d176764, d177881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16205 q selected
  have h2 (q : Pattern) (selected : d176765 q = 0) : d177882 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176765, d177882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176765, d177882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176766 q = 0) : d177883 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176766, d177883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176766, d177883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176767 q = 0) : d177884 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176767, d177884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16205 q selected
    | true =>
      simp only [d176767, d177884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16206 q selected
  have h5 (q : Pattern) (selected : d176768 q = 0) : d177885 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176768, d177885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176768, d177885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176769 q = 0) : d177886 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176769, d177886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176769, d177886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176770 q = 0) : d177887 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176770, d177887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176770, d177887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176771 q = 0) : d177888 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176771, d177888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16206 q selected
    | true =>
      simp only [d176771, d177888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16207 q selected
  have h9 (q : Pattern) (selected : d176772 q = 0) : d177889 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176772, d177889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176772, d177889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176773 q = 0) : d177890 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176773, d177890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176773, d177890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d176774 q = 0) : d177891 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176774, d177891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176774, d177891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d176775 q = 0) : d177892 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176775, d177892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176775, d177892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d176776 q = 0) : d177893 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176776, d177893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d176776, d177893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro16209 (p : Pattern) (selected : d176781 p = 0) : d177898 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176767 q = 0) : d177884 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176767, d177884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16205 q selected
    | true =>
      simp only [d176767, d177884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16206 q selected
  have h2 (q : Pattern) (selected : d176768 q = 0) : d177885 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176768, d177885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176768, d177885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176769 q = 0) : d177886 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176769, d177886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176769, d177886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176771 q = 0) : d177888 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176771, d177888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16206 q selected
    | true =>
      simp only [d176771, d177888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16207 q selected
  have h5 (q : Pattern) (selected : d176772 q = 0) : d177889 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176772, d177889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176772, d177889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176773 q = 0) : d177890 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176773, d177890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176773, d177890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176774 q = 0) : d177891 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176774, d177891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176774, d177891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176779 q = 0) : d177896 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176779, d177896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176779, d177896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d176780 q = 0) : d177897 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176780, d177897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176780, d177897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176781 q = 0) : d177898 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176781, d177898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d176781, d177898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16210 (p : Pattern) (selected : d176787 p = 0) : d177904 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176777 q = 0) : d177894 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176777, d177894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16208 q selected
    | true =>
      simp only [d176777, d177894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176778 q = 0) : d177895 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176778, d177895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176778, d177895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176782 q = 0) : d177899 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176782, d177899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16209 q selected
    | true =>
      simp only [d176782, d177899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176783 q = 0) : d177900 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176783, d177900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176783, d177900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176784 q = 0) : d177901 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176784, d177901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176784, d177901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176785 q = 0) : d177902 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176785, d177902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176785, d177902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176786 q = 0) : d177903 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176786, d177903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176786, d177903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176787 q = 0) : d177904 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176787, d177904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176787, d177904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16211 (p : Pattern) (selected : d176789 p = 0) : d177906 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176771 q = 0) : d177888 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176771, d177888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16206 q selected
    | true =>
      simp only [d176771, d177888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16207 q selected
  have h2 (q : Pattern) (selected : d176772 q = 0) : d177889 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176772, d177889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176772, d177889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176773 q = 0) : d177890 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176773, d177890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176773, d177890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176779 q = 0) : d177896 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176779, d177896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176779, d177896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176788 q = 0) : d177905 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176788, d177905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176788, d177905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176789 q = 0) : d177906 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176789, d177906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176789, d177906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16212 (p : Pattern) (selected : d176795 p = 0) : d177912 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176782 q = 0) : d177899 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176782, d177899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16209 q selected
    | true =>
      simp only [d176782, d177899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176783 q = 0) : d177900 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176783, d177900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176783, d177900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176790 q = 0) : d177907 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176790, d177907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16211 q selected
    | true =>
      simp only [d176790, d177907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176791 q = 0) : d177908 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176791, d177908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176791, d177908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176792 q = 0) : d177909 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176792, d177909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176792, d177909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176793 q = 0) : d177910 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176793, d177910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176793, d177910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176794 q = 0) : d177911 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176794, d177911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176794, d177911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176795 q = 0) : d177912 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176795, d177912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176795, d177912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16213 (p : Pattern) (selected : d15453 p = 0) : d123429 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d15450 q = 0) : d123426 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15450, d123426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15450, d123426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6734 q selected
  have h2 (q : Pattern) (selected : d10200 q = 0) : d101490 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10200, d101490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6734 q selected
    | true =>
      simp only [d10200, d101490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15451 q = 0) : d123427 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15451, d123427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d15451, d123427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10202 q = 0) : d101492 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10202, d101492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10202, d101492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15452 q = 0) : d123428 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15452, d123428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15452, d123428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15453 q = 0) : d123429 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15453, d123429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15453, d123429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16214 (p : Pattern) (selected : d15460 p = 0) : d123439 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d15457 q = 0) : d123436 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15457, d123436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15457, d123436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6735 q selected
  have h2 (q : Pattern) (selected : d10215 q = 0) : d101512 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10215, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6735 q selected
    | true =>
      simp only [d10215, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15458 q = 0) : d123437 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15458, d123437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d15458, d123437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10217 q = 0) : d101514 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10217, d101514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10217, d101514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15459 q = 0) : d123438 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15459, d123438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15459, d123438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15460 q = 0) : d123439 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15460, d123439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15460, d123439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16215 (p : Pattern) (selected : d15469 p = 0) : d123454 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d15466 q = 0) : d123451 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15466, d123451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15466, d123451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6740 q selected
  have h2 (q : Pattern) (selected : d10255 q = 0) : d101562 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10255, d101562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6740 q selected
    | true =>
      simp only [d10255, d101562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15467 q = 0) : d123452 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15467, d123452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d15467, d123452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10257 q = 0) : d101564 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10257, d101564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10257, d101564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15468 q = 0) : d123453 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15468, d123453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15468, d123453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15469 q = 0) : d123454 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15469, d123454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15469, d123454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16216 (p : Pattern) (selected : d176806 p = 0) : d177898 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176797 q = 0) : d177884 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176797, d177884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16213 q selected
    | true =>
      simp only [d176797, d177884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16214 q selected
  have h2 (q : Pattern) (selected : d176798 q = 0) : d177885 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176798, d177885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176798, d177885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176799 q = 0) : d177886 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176799, d177886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176799, d177886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176800 q = 0) : d177888 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176800, d177888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16214 q selected
    | true =>
      simp only [d176800, d177888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16215 q selected
  have h5 (q : Pattern) (selected : d176801 q = 0) : d177889 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176801, d177889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176801, d177889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176802 q = 0) : d177890 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176802, d177890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176802, d177890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176803 q = 0) : d177891 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176803, d177891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176803, d177891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176804 q = 0) : d177896 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176804, d177896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176804, d177896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d176805 q = 0) : d177897 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176805, d177897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176805, d177897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176806 q = 0) : d177898 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176806, d177898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d176806, d177898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16217 (p : Pattern) (selected : d176810 p = 0) : d177906 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176800 q = 0) : d177888 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176800, d177888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16214 q selected
    | true =>
      simp only [d176800, d177888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16215 q selected
  have h2 (q : Pattern) (selected : d176801 q = 0) : d177889 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176801, d177889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176801, d177889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176802 q = 0) : d177890 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176802, d177890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176802, d177890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176804 q = 0) : d177896 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176804, d177896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176804, d177896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176809 q = 0) : d177905 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176809, d177905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176809, d177905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176810 q = 0) : d177906 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176810, d177906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176810, d177906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16218 (p : Pattern) (selected : d176816 p = 0) : d177912 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176807 q = 0) : d177899 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176807, d177899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16216 q selected
    | true =>
      simp only [d176807, d177899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176808 q = 0) : d177900 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176808, d177900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176808, d177900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176811 q = 0) : d177907 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176811, d177907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16217 q selected
    | true =>
      simp only [d176811, d177907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176812 q = 0) : d177908 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176812, d177908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176812, d177908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176813 q = 0) : d177909 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176813, d177909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176813, d177909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176814 q = 0) : d177910 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176814, d177910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176814, d177910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176815 q = 0) : d177911 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176815, d177911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176815, d177911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176816 q = 0) : d177912 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176816, d177912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176816, d177912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16219 (p : Pattern) (selected : d176820 p = 0) : d177917 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176811 q = 0) : d177907 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176811, d177907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16217 q selected
    | true =>
      simp only [d176811, d177907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176812 q = 0) : d177908 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176812, d177908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176812, d177908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176817 q = 0) : d177914 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176817, d177914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176817, d177914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176818 q = 0) : d177915 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176818, d177915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176818, d177915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176819 q = 0) : d177916 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176819, d177916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176819, d177916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176820 q = 0) : d177917 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176820, d177917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176820, d177917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16220 (p : Pattern) (selected : d176828 p = 0) : d177925 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176767 q = 0) : d177884 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176767, d177884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16205 q selected
    | true =>
      simp only [d176767, d177884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16206 q selected
  have h2 (q : Pattern) (selected : d176768 q = 0) : d177885 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176768, d177885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176768, d177885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176769 q = 0) : d177886 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176769, d177886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176769, d177886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176771 q = 0) : d177888 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176771, d177888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16206 q selected
    | true =>
      simp only [d176771, d177888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16207 q selected
  have h5 (q : Pattern) (selected : d176772 q = 0) : d177889 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176772, d177889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176772, d177889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176773 q = 0) : d177890 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176773, d177890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176773, d177890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176774 q = 0) : d177891 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176774, d177891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176774, d177891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176823 q = 0) : d177920 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176823, d177920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16206 q selected
    | true =>
      simp only [d176823, d177920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d176824 q = 0) : d177921 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176824, d177921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176824, d177921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176825 q = 0) : d177922 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176825, d177922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176825, d177922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d176826 q = 0) : d177923 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176826, d177923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d176826, d177923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d176827 q = 0) : d177924 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176827, d177924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176827, d177924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d176828 q = 0) : d177925 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176828, d177925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d176828, d177925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro16221 (p : Pattern) (selected : d176834 p = 0) : d177931 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176829 q = 0) : d177926 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176829, d177926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16220 q selected
    | true =>
      simp only [d176829, d177926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176830 q = 0) : d177927 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176830, d177927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176830, d177927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176831 q = 0) : d177928 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176831, d177928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176831, d177928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176832 q = 0) : d177929 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176832, d177929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176832, d177929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176833 q = 0) : d177930 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176833, d177930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176833, d177930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176834 q = 0) : d177931 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176834, d177931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176834, d177931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16222 (p : Pattern) (selected : d176840 p = 0) : d177937 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176796 q = 0) : d177913 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176796, d177913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16210 q selected
    | true =>
      simp only [d176796, d177913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16212 q selected
  have h2 (q : Pattern) (selected : d176821 q = 0) : d177918 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176821, d177918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16218 q selected
    | true =>
      simp only [d176821, d177918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16219 q selected
  have h3 (q : Pattern) (selected : d176822 q = 0) : d177919 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176822, d177919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d176822, d177919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176835 q = 0) : d177932 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176835, d177932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16221 q selected
    | true =>
      simp only [d176835, d177932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176836 q = 0) : d177933 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176836, d177933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176836, d177933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176837 q = 0) : d177934 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176837, d177934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176837, d177934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176838 q = 0) : d177935 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176838, d177935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176838, d177935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176839 q = 0) : d177936 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176839, d177936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176839, d177936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d176840 q = 0) : d177937 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176840, d177937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176840, d177937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro16223 (p : Pattern) (selected : d176845 p = 0) : d177917 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176790 q = 0) : d177907 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176790, d177907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16211 q selected
    | true =>
      simp only [d176790, d177907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176791 q = 0) : d177908 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176791, d177908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176791, d177908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176842 q = 0) : d177914 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176842, d177914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176842, d177914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176843 q = 0) : d177915 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176843, d177915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176843, d177915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176844 q = 0) : d177916 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176844, d177916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176844, d177916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176845 q = 0) : d177917 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176845, d177917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176845, d177917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16224 (p : Pattern) (selected : d176851 p = 0) : d177944 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176846 q = 0) : d177939 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176846, d177939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16223 q selected
    | true =>
      simp only [d176846, d177939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176847 q = 0) : d177940 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176847, d177940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176847, d177940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176848 q = 0) : d177941 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176848, d177941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176848, d177941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176849 q = 0) : d177942 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176849, d177942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176849, d177942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176850 q = 0) : d177943 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176850, d177943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176850, d177943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176851 q = 0) : d177944 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176851, d177944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176851, d177944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16225 (p : Pattern) (selected : d176857 p = 0) : d177950 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176626 q = 0) : d177771 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d176626, d177771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176626, d177771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16170 q selected
  have h2 (q : Pattern) (selected : d176627 q = 0) : d177772 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d176627, d177772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d176627, d177772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d176636 q = 0) : d177781 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d176636, d177781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16170 q selected
    | true =>
      simp only [d176636, d177781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16173 q selected
  have h4 (q : Pattern) (selected : d176637 q = 0) : d177782 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d176637, d177782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176637, d177782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176638 q = 0) : d177783 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d176638, d177783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176638, d177783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176737 q = 0) : d177854 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d176737, d177854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16190 q selected
    | true =>
      simp only [d176737, d177854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16199 q selected
  have h7 (q : Pattern) (selected : d176750 q = 0) : d177867 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d176750, d177867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16200 q selected
    | true =>
      simp only [d176750, d177867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16201 q selected
  have h8 (q : Pattern) (selected : d176751 q = 0) : d177868 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d176751, d177868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176751, d177868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d176752 q = 0) : d177869 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d176752, d177869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d176752, d177869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d176753 q = 0) : d177870 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d176753, d177870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176753, d177870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d176757 q = 0) : d177874 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d176757, d177874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176757, d177874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16202 q selected
  have h12 (q : Pattern) (selected : d176759 q = 0) : d177876 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d176759, d177876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176759, d177876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16203 q selected
  have h13 (q : Pattern) (selected : d176760 q = 0) : d177877 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d176760, d177877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d176760, d177877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d176761 q = 0) : d177878 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d176761, d177878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d176761, d177878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d176762 q = 0) : d177879 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d176762, d177879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d176762, d177879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d176763 q = 0) : d177880 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d176763, d177880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d176763, d177880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d176841 q = 0) : d177938 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d176841, d177938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176841, d177938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16222 q selected
  have h18 (q : Pattern) (selected : d176852 q = 0) : d177945 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d176852, d177945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176852, d177945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16224 q selected
  have h19 (q : Pattern) (selected : d176853 q = 0) : d177946 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d176853, d177946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d176853, d177946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d176854 q = 0) : d177947 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d176854, d177947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d176854, d177947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d176855 q = 0) : d177948 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d176855, d177948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d176855, d177948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d176856 q = 0) : d177949 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d176856, d177949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d176856, d177949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d176857 q = 0) : d177950 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d176857, d177950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d176857, d177950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro16226 (p : Pattern) (selected : d176863 p = 0) : d177956 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176858 q = 0) : d177951 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d176858, d177951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176858, d177951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16225 q selected
  have h2 (q : Pattern) (selected : d176859 q = 0) : d177952 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d176859, d177952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176859, d177952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176860 q = 0) : d177953 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d176860, d177953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176860, d177953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176861 q = 0) : d177954 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d176861, d177954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176861, d177954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176862 q = 0) : d177955 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d176862, d177955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176862, d177955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176863 q = 0) : d177956 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d176863, d177956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176863, d177956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16227 (p : Pattern) (selected : d13676 p = 0) : d113866 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10353 q = 0) : d101674 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6756 q selected
    | true =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10355 q = 0) : d101676 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13675 q = 0) : d113865 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13675, d113865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13675, d113865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13676 q = 0) : d113866 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13676, d113866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13676, d113866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16228 (p : Pattern) (selected : d15549 p = 0) : d123548 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10371 q = 0) : d101692 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6759 q selected
    | true =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10373 q = 0) : d101694 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10373, d101694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10373, d101694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15548 q = 0) : d123547 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15548, d123547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15548, d123547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d15549 q = 0) : d123548 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15549, d123548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15549, d123548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16229 (p : Pattern) (selected : d15556 p = 0) : d123555 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10412 q = 0) : d101733 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6764 q selected
    | true =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10414 q = 0) : d101735 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10414, d101735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10414, d101735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15555 q = 0) : d123554 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15555, d123554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15555, d123554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d15556 q = 0) : d123555 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15556, d123555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15556, d123555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16230 (p : Pattern) (selected : d176877 p = 0) : d177970 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176868 q = 0) : d177961 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176868, d177961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16227 q selected
    | true =>
      simp only [d176868, d177961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16228 q selected
  have h2 (q : Pattern) (selected : d176869 q = 0) : d177962 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176869, d177962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176869, d177962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176870 q = 0) : d177963 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176870, d177963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176870, d177963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176871 q = 0) : d177964 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176871, d177964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16228 q selected
    | true =>
      simp only [d176871, d177964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16229 q selected
  have h5 (q : Pattern) (selected : d176872 q = 0) : d177965 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176872, d177965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176872, d177965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176873 q = 0) : d177966 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176873, d177966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176873, d177966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176874 q = 0) : d177967 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176874, d177967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176874, d177967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176875 q = 0) : d177968 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176875, d177968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176875, d177968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d176876 q = 0) : d177969 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176876, d177969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176876, d177969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176877 q = 0) : d177970 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176877, d177970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d176877, d177970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16231 (p : Pattern) (selected : d176881 p = 0) : d177974 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176871 q = 0) : d177964 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176871, d177964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16228 q selected
    | true =>
      simp only [d176871, d177964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16229 q selected
  have h2 (q : Pattern) (selected : d176872 q = 0) : d177965 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176872, d177965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176872, d177965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176873 q = 0) : d177966 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176873, d177966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176873, d177966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176875 q = 0) : d177968 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176875, d177968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176875, d177968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176880 q = 0) : d177973 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176880, d177973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176880, d177973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176881 q = 0) : d177974 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176881, d177974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176881, d177974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16232 (p : Pattern) (selected : d176887 p = 0) : d177980 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176878 q = 0) : d177971 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176878, d177971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16230 q selected
    | true =>
      simp only [d176878, d177971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176879 q = 0) : d177972 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176879, d177972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176879, d177972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176882 q = 0) : d177975 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176882, d177975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16231 q selected
    | true =>
      simp only [d176882, d177975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176883 q = 0) : d177976 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176883, d177976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176883, d177976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176884 q = 0) : d177977 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176884, d177977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176884, d177977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176885 q = 0) : d177978 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176885, d177978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176885, d177978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176886 q = 0) : d177979 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176886, d177979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176886, d177979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176887 q = 0) : d177980 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176887, d177980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176887, d177980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16233 (p : Pattern) (selected : d176891 p = 0) : d177984 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176882 q = 0) : d177975 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176882, d177975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16231 q selected
    | true =>
      simp only [d176882, d177975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176883 q = 0) : d177976 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176883, d177976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176883, d177976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176888 q = 0) : d177981 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176888, d177981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176888, d177981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176889 q = 0) : d177982 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176889, d177982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176889, d177982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176890 q = 0) : d177983 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176890, d177983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176890, d177983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176891 q = 0) : d177984 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176891, d177984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176891, d177984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16234 (p : Pattern) (selected : d176897 p = 0) : d177990 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176892 q = 0) : d177985 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176892, d177985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16232 q selected
    | true =>
      simp only [d176892, d177985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16233 q selected
  have h2 (q : Pattern) (selected : d176893 q = 0) : d177986 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176893, d177986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176893, d177986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176894 q = 0) : d177987 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176894, d177987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176894, d177987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176895 q = 0) : d177988 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176895, d177988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176895, d177988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176896 q = 0) : d177989 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176896, d177989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176896, d177989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176897 q = 0) : d177990 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176897, d177990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176897, d177990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16235 (p : Pattern) (selected : d176900 p = 0) : d177993 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176878 q = 0) : d177971 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176878, d177971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16230 q selected
    | true =>
      simp only [d176878, d177971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176879 q = 0) : d177972 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176879, d177972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176879, d177972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176882 q = 0) : d177975 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176882, d177975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16231 q selected
    | true =>
      simp only [d176882, d177975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176883 q = 0) : d177976 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176883, d177976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176883, d177976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176884 q = 0) : d177977 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176884, d177977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176884, d177977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176885 q = 0) : d177978 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176885, d177978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176885, d177978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176886 q = 0) : d177979 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176886, d177979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176886, d177979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176900 q = 0) : d177993 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176900, d177993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176900, d177993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16236 (p : Pattern) (selected : d176901 p = 0) : d177994 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176882 q = 0) : d177975 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176882, d177975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16231 q selected
    | true =>
      simp only [d176882, d177975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176883 q = 0) : d177976 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176883, d177976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176883, d177976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176888 q = 0) : d177981 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176888, d177981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176888, d177981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176889 q = 0) : d177982 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176889, d177982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176889, d177982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176890 q = 0) : d177983 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176890, d177983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176890, d177983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176901 q = 0) : d177994 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176901, d177994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176901, d177994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16237 (p : Pattern) (selected : d176907 p = 0) : d178000 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176892 q = 0) : d177985 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176892, d177985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16232 q selected
    | true =>
      simp only [d176892, d177985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16233 q selected
  have h2 (q : Pattern) (selected : d176893 q = 0) : d177986 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176893, d177986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176893, d177986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176894 q = 0) : d177987 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176894, d177987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176894, d177987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176895 q = 0) : d177988 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176895, d177988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176895, d177988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176896 q = 0) : d177989 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176896, d177989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176896, d177989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176902 q = 0) : d177995 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176902, d177995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16235 q selected
    | true =>
      simp only [d176902, d177995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16236 q selected
  have h7 (q : Pattern) (selected : d176903 q = 0) : d177996 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176903, d177996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176903, d177996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176904 q = 0) : d177997 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176904, d177997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176904, d177997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d176905 q = 0) : d177998 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176905, d177998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176905, d177998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176906 q = 0) : d177999 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176906, d177999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176906, d177999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d176907 q = 0) : d178000 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176907, d178000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176907, d178000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16238 (p : Pattern) (selected : d176912 p = 0) : d178005 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176878 q = 0) : d177971 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176878, d177971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16230 q selected
    | true =>
      simp only [d176878, d177971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176879 q = 0) : d177972 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176879, d177972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176879, d177972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176882 q = 0) : d177975 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176882, d177975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16231 q selected
    | true =>
      simp only [d176882, d177975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176883 q = 0) : d177976 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176883, d177976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176883, d177976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176884 q = 0) : d177977 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176884, d177977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176884, d177977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176885 q = 0) : d177978 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176885, d177978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176885, d177978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176911 q = 0) : d178004 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176911, d178004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176911, d178004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176912 q = 0) : d178005 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176912, d178005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176912, d178005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16239 (p : Pattern) (selected : d176914 p = 0) : d178007 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176882 q = 0) : d177975 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176882, d177975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16231 q selected
    | true =>
      simp only [d176882, d177975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176883 q = 0) : d177976 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176883, d177976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176883, d177976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176888 q = 0) : d177981 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176888, d177981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176888, d177981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176889 q = 0) : d177982 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176889, d177982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176889, d177982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176913 q = 0) : d178006 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176913, d178006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176913, d178006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176914 q = 0) : d178007 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176914, d178007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176914, d178007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16240 (p : Pattern) (selected : d176921 p = 0) : d178014 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176878 q = 0) : d177971 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176878, d177971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16230 q selected
    | true =>
      simp only [d176878, d177971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176879 q = 0) : d177972 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176879, d177972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176879, d177972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176882 q = 0) : d177975 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176882, d177975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16231 q selected
    | true =>
      simp only [d176882, d177975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176883 q = 0) : d177976 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176883, d177976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176883, d177976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176884 q = 0) : d177977 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176884, d177977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176884, d177977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176919 q = 0) : d178012 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176919, d178012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176919, d178012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176920 q = 0) : d178013 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176920, d178013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176920, d178013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176921 q = 0) : d178014 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176921, d178014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176921, d178014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16241 (p : Pattern) (selected : d176924 p = 0) : d178017 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176882 q = 0) : d177975 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176882, d177975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16231 q selected
    | true =>
      simp only [d176882, d177975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176883 q = 0) : d177976 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176883, d177976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176883, d177976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176888 q = 0) : d177981 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176888, d177981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176888, d177981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176922 q = 0) : d178015 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176922, d178015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176922, d178015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176923 q = 0) : d178016 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176923, d178016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176923, d178016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176924 q = 0) : d178017 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176924, d178017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176924, d178017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16242 (p : Pattern) (selected : d176933 p = 0) : d178026 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176928 q = 0) : d178021 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176928, d178021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176928, d178021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16227 q selected
  have h2 (q : Pattern) (selected : d176929 q = 0) : d178022 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176929, d178022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176929, d178022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176930 q = 0) : d178023 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176930, d178023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176930, d178023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176868 q = 0) : d177961 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176868, d177961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16227 q selected
    | true =>
      simp only [d176868, d177961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16228 q selected
  have h5 (q : Pattern) (selected : d176869 q = 0) : d177962 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176869, d177962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176869, d177962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176870 q = 0) : d177963 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176870, d177963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176870, d177963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176931 q = 0) : d178024 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176931, d178024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176931, d178024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176871 q = 0) : d177964 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176871, d177964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16228 q selected
    | true =>
      simp only [d176871, d177964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16229 q selected
  have h9 (q : Pattern) (selected : d176872 q = 0) : d177965 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176872, d177965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176872, d177965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176873 q = 0) : d177966 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176873, d177966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176873, d177966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d176874 q = 0) : d177967 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176874, d177967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176874, d177967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d176932 q = 0) : d178025 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176932, d178025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176932, d178025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d176933 q = 0) : d178026 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176933, d178026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d176933, d178026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro16243 (p : Pattern) (selected : d176939 p = 0) : d178032 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176934 q = 0) : d178027 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176934, d178027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16242 q selected
    | true =>
      simp only [d176934, d178027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176935 q = 0) : d178028 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176935, d178028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176935, d178028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176878 q = 0) : d177971 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176878, d177971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16230 q selected
    | true =>
      simp only [d176878, d177971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176879 q = 0) : d177972 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176879, d177972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176879, d177972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176936 q = 0) : d178029 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176936, d178029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176936, d178029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176937 q = 0) : d178030 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176937, d178030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176937, d178030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176938 q = 0) : d178031 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176938, d178031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176938, d178031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176939 q = 0) : d178032 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176939, d178032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176939, d178032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16244 (p : Pattern) (selected : d15650 p = 0) : d113866 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10468 q = 0) : d101674 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10468, d101674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6773 q selected
    | true =>
      simp only [d10468, d101674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10470 q = 0) : d101676 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10470, d101676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10470, d101676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15649 q = 0) : d113865 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15649, d113865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15649, d113865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d15650 q = 0) : d113866 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15650, d113866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15650, d113866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16245 (p : Pattern) (selected : d15655 p = 0) : d123548 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10482 q = 0) : d101692 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10482, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6774 q selected
    | true =>
      simp only [d10482, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10484 q = 0) : d101694 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10484, d101694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10484, d101694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15654 q = 0) : d123547 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15654, d123547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15654, d123547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d15655 q = 0) : d123548 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15655, d123548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15655, d123548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16246 (p : Pattern) (selected : d15662 p = 0) : d123555 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10521 q = 0) : d101733 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10521, d101733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6779 q selected
    | true =>
      simp only [d10521, d101733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10523 q = 0) : d101735 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10523, d101735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10523, d101735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15661 q = 0) : d123554 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15661, d123554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15661, d123554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d15662 q = 0) : d123555 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15662, d123555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15662, d123555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16247 (p : Pattern) (selected : d176950 p = 0) : d177970 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176941 q = 0) : d177961 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176941, d177961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16244 q selected
    | true =>
      simp only [d176941, d177961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16245 q selected
  have h2 (q : Pattern) (selected : d176942 q = 0) : d177962 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176942, d177962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176942, d177962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176943 q = 0) : d177963 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176943, d177963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176943, d177963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176944 q = 0) : d177964 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176944, d177964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16245 q selected
    | true =>
      simp only [d176944, d177964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16246 q selected
  have h5 (q : Pattern) (selected : d176945 q = 0) : d177965 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176945, d177965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176945, d177965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176946 q = 0) : d177966 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176946, d177966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176946, d177966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176947 q = 0) : d177967 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176947, d177967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176947, d177967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176948 q = 0) : d177968 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176948, d177968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176948, d177968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d176949 q = 0) : d177969 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176949, d177969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176949, d177969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176950 q = 0) : d177970 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176950, d177970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d176950, d177970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16248 (p : Pattern) (selected : d176954 p = 0) : d177974 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176944 q = 0) : d177964 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176944, d177964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16245 q selected
    | true =>
      simp only [d176944, d177964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16246 q selected
  have h2 (q : Pattern) (selected : d176945 q = 0) : d177965 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176945, d177965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176945, d177965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176946 q = 0) : d177966 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176946, d177966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176946, d177966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176948 q = 0) : d177968 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176948, d177968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176948, d177968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176953 q = 0) : d177973 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176953, d177973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176953, d177973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176954 q = 0) : d177974 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176954, d177974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176954, d177974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16249 (p : Pattern) (selected : d176960 p = 0) : d177980 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176951 q = 0) : d177971 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176951, d177971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16247 q selected
    | true =>
      simp only [d176951, d177971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176952 q = 0) : d177972 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176952, d177972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176952, d177972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176955 q = 0) : d177975 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176955, d177975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16248 q selected
    | true =>
      simp only [d176955, d177975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176956 q = 0) : d177976 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176956, d177976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176956, d177976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176957 q = 0) : d177977 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176957, d177977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176957, d177977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176958 q = 0) : d177978 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176958, d177978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176958, d177978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176959 q = 0) : d177979 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176959, d177979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176959, d177979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176960 q = 0) : d177980 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176960, d177980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176960, d177980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
end NetHack.Soko22Hazard87
