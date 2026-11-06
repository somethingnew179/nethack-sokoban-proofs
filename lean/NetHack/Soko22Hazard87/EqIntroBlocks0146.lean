import NetHack.Soko22Hazard87.EqIntroBlocks0145
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro36500 (p : Pattern) (selected : d344714 p = 1) : d349316 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d344709 q = 1) : d349311 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d344709, d349311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d344709, d349311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36499 q selected
  have h2 (q : Pattern) (selected : d344710 q = 1) : d349312 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d344710, d349312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d344710, d349312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d344711 q = 1) : d349313 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d344711, d349313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d344711, d349313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d344712 q = 1) : d349314 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d344712, d349314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d344712, d349314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d344713 q = 1) : d349315 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d344713, d349315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d344713, d349315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d344714 q = 1) : d349316 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d344714, d349316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d344714, d349316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro36501 (p : Pattern) (selected : d344847 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d203201 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19726 q selected
    | true =>
      simp only [d203201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203202 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d203202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d203642 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19760 q selected
    | true =>
      simp only [d203642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d203643 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d203643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d344845 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d344845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d344845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d344846 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d344846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d344846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d203207 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19705 q selected
    | true =>
      simp only [d203207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19728 q selected
  have h8 (q : Pattern) (selected : d203208 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d203208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d202615 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d202615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19690 q selected
    | true =>
      simp only [d202615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d202616 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d202616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d202616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d203216 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d203216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d203216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d203217 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d203217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d203217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d344847 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d344847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d344847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro36502 (p : Pattern) (selected : d344852 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d203207 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19705 q selected
    | true =>
      simp only [d203207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19728 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d203208 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d203208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d202615 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d202615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19690 q selected
    | true =>
      simp only [d202615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d202616 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d202616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d202616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d203216 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d203216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203217 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d203217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d202855 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d202855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d202855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d202856 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d202856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d202856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d344852 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d344852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d344852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro36503 (p : Pattern) (selected : d344860 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d202851 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d202851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19705 q selected
    | true =>
      simp only [d202851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d202852 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d202852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d202852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d344858 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d344858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d344858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d344859 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d344859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d344859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d202615 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d202615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19690 q selected
    | true =>
      simp only [d202615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d202616 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d202616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d202616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d202855 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d202855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d202855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d202856 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d202856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d202856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d344860 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d344860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d344860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro36504 (p : Pattern) (selected : d344866 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d344848 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d344848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36501 q selected
    | true =>
      simp only [d344848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d344849 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d344849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d344849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d344850 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d344850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d344850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d344851 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d344851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d344851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d344853 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d344853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36502 q selected
    | true =>
      simp only [d344853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d344854 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d344854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d344854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d344855 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d344855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d344855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d344856 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d344856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d344856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d344857 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d344857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d344857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d344861 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d344861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36503 q selected
    | true =>
      simp only [d344861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d344862 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d344862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d344862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d344863 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d344863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d344863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d344864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d344864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d344864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d202864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d202864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19707 q selected
    | true =>
      simp only [d202864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d202865 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d202865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d202865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d202866 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d202866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d202867 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d202867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d202867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d344865 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d344865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d344865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d344866 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d344866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d344866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro36505 (p : Pattern) (selected : d344867 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d203207 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19705 q selected
    | true =>
      simp only [d203207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19728 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d203208 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d203208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d202615 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d202615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19690 q selected
    | true =>
      simp only [d202615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d202616 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d202616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d202616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d203216 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d203216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203217 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d203217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d203218 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19690 q selected
    | true =>
      simp only [d203218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19675 q selected
  have h8 (q : Pattern) (selected : d203219 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d203219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d202440 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d202440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19675 q selected
    | true =>
      simp only [d202440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h10 (q : Pattern) (selected : d202441 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d202441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d202441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h11 (q : Pattern) (selected : d203233 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d203233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d203233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d203234 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d203234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d203234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h13 (q : Pattern) (selected : d344867 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d344867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d344867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro36506 (p : Pattern) (selected : d344872 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d203218 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19690 q selected
    | true =>
      simp only [d203218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19675 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d203219 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d203219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d202440 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d202440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19675 q selected
    | true =>
      simp only [d202440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d202441 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d202441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d202441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d203233 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d203233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d203233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d203234 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d203234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d202442 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d202442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d202442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d202443 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d202443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d202443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d344872 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d344872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d344872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro36507 (p : Pattern) (selected : d344879 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d344868 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d344868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36505 q selected
    | true =>
      simp only [d344868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d344869 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d344869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d344869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d344870 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d344870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d344870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d344871 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d344871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d344871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d344873 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d344873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36506 q selected
    | true =>
      simp only [d344873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d344874 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d344874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d344874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d344875 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d344875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d344875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d344876 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d344876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d344876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d344877 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d344877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d344877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d202864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d202864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19707 q selected
    | true =>
      simp only [d202864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d202865 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d202865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d202865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d202866 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d202866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d202866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d202867 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d202867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d202867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d344878 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d344878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d344878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d344879 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d344879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d344879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro36508 (p : Pattern) (selected : d344884 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d344873 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d344873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36506 q selected
    | true =>
      simp only [d344873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d344874 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d344874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d344874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d344875 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d344875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d344875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d344876 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d344876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d344876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d344883 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d344883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d344883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d344884 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d344884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d344884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36509 (p : Pattern) (selected : d344891 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d344880 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d344880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36504 q selected
    | true =>
      simp only [d344880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36507 q selected
  have h2 (q : Pattern) (selected : d344881 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d344881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d344881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d344882 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d344882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d344882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d344885 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d344885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36507 q selected
    | true =>
      simp only [d344885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36508 q selected
  have h5 (q : Pattern) (selected : d344886 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d344886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d344886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d344887 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d344887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d344887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d344888 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d344888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d344888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d344889 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d344889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d344889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d344890 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d344890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d344890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d344891 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d344891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d344891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro36510 (p : Pattern) (selected : d344895 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d344885 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d344885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36507 q selected
    | true =>
      simp only [d344885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36508 q selected
  have h2 (q : Pattern) (selected : d344886 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d344886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d344886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d344887 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d344887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d344887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d344889 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d344889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d344889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d344894 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d344894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d344894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d344895 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d344895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d344895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36511 (p : Pattern) (selected : d344901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d344892 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d344892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36509 q selected
    | true =>
      simp only [d344892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d344893 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d344893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d344893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d344896 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d344896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36510 q selected
    | true =>
      simp only [d344896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d344897 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d344897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d344897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d344898 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d344898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d344898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d344899 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d344899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d344899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d344900 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d344900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d344900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d344901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d344901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d344901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro36512 (p : Pattern) (selected : d344905 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d344896 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d344896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36510 q selected
    | true =>
      simp only [d344896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d344897 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d344897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d344897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d344902 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d344902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d344902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d344903 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d344903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d344903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d344904 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d344904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d344904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d344905 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d344905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d344905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro36513 (p : Pattern) (selected : d344917 p = 1) : d349323 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d344794 q = 1) : d344794 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d344803 q = 1) : d344803 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d344844 q = 1) : d344844 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d344906 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d344906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36511 q selected
    | true =>
      simp only [d344906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36512 q selected
  have h5 (q : Pattern) (selected : d344907 q = 1) : d349319 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d344907, d349319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d344907, d349319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d344913 q = 1) : d344913 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d344914 q = 1) : d349320 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d344914, d349320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d344914, d349320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d344915 q = 1) : d349321 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d344915, d349321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d344915, d349321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d344916 q = 1) : d349322 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d344916, d349322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d344916, d349322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d344917 q = 1) : d349323 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d344917, d349323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d344917, d349323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro36514 (p : Pattern) (selected : d344931 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d344892 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d344892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36509 q selected
    | true =>
      simp only [d344892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d344893 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d344893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d344893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d344896 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d344896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36510 q selected
    | true =>
      simp only [d344896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d344897 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d344897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d344897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d344898 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d344898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d344898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d344899 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d344899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d344899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d344900 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d344900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d344900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d344931 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d344931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d344931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro36515 (p : Pattern) (selected : d344932 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d344896 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d344896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36510 q selected
    | true =>
      simp only [d344896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d344897 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d344897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d344897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d344902 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d344902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d344902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d344903 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d344903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d344903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d344904 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d344904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d344904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d344932 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d344932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d344932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36516 (p : Pattern) (selected : d344941 p = 1) : d349328 p = 1 := by
  have h0 (q : Pattern) (selected : d344794 q = 1) : d344794 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d344803 q = 1) : d344803 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d344844 q = 1) : d344844 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d344906 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d344906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36511 q selected
    | true =>
      simp only [d344906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36512 q selected
  have h4 (q : Pattern) (selected : d344907 q = 1) : d349319 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d344907, d349319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d344907, d349319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d344913 q = 1) : d344913 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d344914 q = 1) : d349320 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d344914, d349320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d344914, d349320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d344915 q = 1) : d349321 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d344915, d349321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d344915, d349321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d344916 q = 1) : d349322 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d344916, d349322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d344916, d349322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d344923 q = 1) : d344923 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d344928 q = 1) : d344928 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d344930 q = 1) : d344930 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d344933 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d344933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36514 q selected
    | true =>
      simp only [d344933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36515 q selected
  have h13 (q : Pattern) (selected : d344934 q = 1) : d349324 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d344934, d349324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d344934, d349324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d344937 q = 1) : d344937 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d344938 q = 1) : d349325 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d344938, d349325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d344938, d349325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d344939 q = 1) : d349326 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d344939, d349326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d344939, d349326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d344940 q = 1) : d349327 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d344940, d349327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d344940, d349327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d344941 q = 1) : d349328 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d344941, d349328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d344941, d349328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro36517 (p : Pattern) (selected : d344961 p = 1) : d349335 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d344930 q = 1) : d344930 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d344933 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d344933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36514 q selected
    | true =>
      simp only [d344933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36515 q selected
  have h3 (q : Pattern) (selected : d344934 q = 1) : d349324 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d344934, d349324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d344934, d349324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d344937 q = 1) : d344937 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d344938 q = 1) : d349325 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d344938, d349325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d344938, d349325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d344959 q = 1) : d349333 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d344959, d349333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d344959, d349333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d344960 q = 1) : d349334 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d344960, d349334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d344960, d349334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d344961 q = 1) : d349335 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d344961, d349335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d344961, d349335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro36518 (p : Pattern) (selected : d345063 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345049 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d345049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36501 q selected
  have h2 (q : Pattern) (selected : d344848 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d344848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36501 q selected
    | true =>
      simp only [d344848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d345050 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d345050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d345050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d344849 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d344849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d344849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d345051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d345051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d345052 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d345052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d345052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d345053 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d345053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36502 q selected
  have h8 (q : Pattern) (selected : d344853 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d344853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36502 q selected
    | true =>
      simp only [d344853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d345054 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d345054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d345054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d344854 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d344854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d344854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d345055 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d345055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d345055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d345056 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d345056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d345056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d345057 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d345057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d345057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d345058 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d345058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36503 q selected
  have h15 (q : Pattern) (selected : d344861 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d344861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36503 q selected
    | true =>
      simp only [d344861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d345059 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d345059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d345059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d344862 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d344862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d344862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d345060 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d345060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d345060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d345061 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d345061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d345061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d203000 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19707 q selected
  have h21 (q : Pattern) (selected : d202864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d202864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19707 q selected
    | true =>
      simp only [d202864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d203001 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d203001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d202865 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d202865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d202865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d203002 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d203002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d203003 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d203003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d345062 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d345062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d345062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d345063 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d345063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d345063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro36519 (p : Pattern) (selected : d345074 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345064 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d345064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36505 q selected
  have h2 (q : Pattern) (selected : d344868 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d344868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36505 q selected
    | true =>
      simp only [d344868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d345065 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d345065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d345065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d344869 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d344869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d344869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d345066 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d345066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d345067 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d345067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d345067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d345068 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d345068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36506 q selected
  have h8 (q : Pattern) (selected : d344873 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d344873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36506 q selected
    | true =>
      simp only [d344873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d345069 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d345069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d345069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d344874 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d344874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d344874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d345070 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d345070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d345070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d345071 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d345071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d345071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d345072 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d345072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d345072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d203000 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d203000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d203000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19707 q selected
  have h15 (q : Pattern) (selected : d202864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d202864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19707 q selected
    | true =>
      simp only [d202864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d203001 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d203001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d203001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d202865 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d202865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d202865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d203002 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d203002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d203002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d203003 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d203003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d203003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d345073 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d345073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d345073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d345074 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d345074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d345074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro36520 (p : Pattern) (selected : d345079 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345068 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d345068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36506 q selected
  have h2 (q : Pattern) (selected : d344873 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d344873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36506 q selected
    | true =>
      simp only [d344873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d345069 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d345069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d345069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d344874 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d344874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d344874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d345070 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d345070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d345071 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d345071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d345071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d345078 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d345078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d345078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d345079 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d345079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d345079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro36521 (p : Pattern) (selected : d345086 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345075 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d345075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36518 q selected
    | true =>
      simp only [d345075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36519 q selected
  have h2 (q : Pattern) (selected : d345076 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d345076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d345077 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d345077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d345080 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d345080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36519 q selected
    | true =>
      simp only [d345080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36520 q selected
  have h5 (q : Pattern) (selected : d345081 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d345081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d345082 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d345082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d345083 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d345083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d345084 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d345084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d345084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d345085 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d345085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d345085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d345086 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d345086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d345086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro36522 (p : Pattern) (selected : d345090 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345080 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d345080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36519 q selected
    | true =>
      simp only [d345080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36520 q selected
  have h2 (q : Pattern) (selected : d345081 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d345081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d345082 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d345082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d345084 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d345084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d345089 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d345089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d345089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d345090 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d345090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d345090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36523 (p : Pattern) (selected : d345096 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345087 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d345087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36521 q selected
    | true =>
      simp only [d345087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d345088 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d345088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d345091 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d345091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36522 q selected
    | true =>
      simp only [d345091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d345092 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d345092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d345093 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d345093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d345093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d345094 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d345094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d345094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d345095 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d345095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d345095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d345096 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d345096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d345096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro36524 (p : Pattern) (selected : d345100 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345091 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d345091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36522 q selected
    | true =>
      simp only [d345091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d345092 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d345092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d345097 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d345097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d345097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d345098 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d345098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d345099 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d345099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d345099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d345100 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d345100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d345100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36525 (p : Pattern) (selected : d345112 p = 1) : d349345 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345048 q = 1) : d345048 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d345101 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d345101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36523 q selected
    | true =>
      simp only [d345101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36524 q selected
  have h3 (q : Pattern) (selected : d345102 q = 1) : d349341 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d345102, d349341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d345102, d349341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d345108 q = 1) : d345108 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d345109 q = 1) : d349342 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d345109, d349342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345109, d349342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d345110 q = 1) : d349343 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d345110, d349343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345110, d349343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d345111 q = 1) : d349344 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d345111, d349344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345111, d349344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d345112 q = 1) : d349345 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d345112, d349345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345112, d349345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro36526 (p : Pattern) (selected : d345129 p = 1) : d349351 p = 1 := by
  have h0 (q : Pattern) (selected : d344786 q = 1) : d344786 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d344942 q = 1) : d349329 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d344942, d349329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36513 q selected
    | true =>
      simp only [d344942, d349329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36516 q selected
  have h2 (q : Pattern) (selected : d344955 q = 1) : d344955 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d344956 q = 1) : d349330 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d344956, d349330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d344956, d349330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d344957 q = 1) : d349331 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d344957, d349331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d344957, d349331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d344958 q = 1) : d349332 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d344958, d349332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d344958, d349332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d344962 q = 1) : d349336 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d344962, d349336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d344962, d349336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36517 q selected
  have h8 (q : Pattern) (selected : d344964 q = 1) : d344964 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d344965 q = 1) : d349337 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d344965, d349337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d344965, d349337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d344966 q = 1) : d349338 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d344966, d349338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d344966, d349338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d344967 q = 1) : d349339 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d344967, d349339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d344967, d349339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d344968 q = 1) : d349340 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d344968, d349340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d344968, d349340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d345113 q = 1) : d349346 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d345113, d349346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d345113, d349346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36525 q selected
  have h14 (q : Pattern) (selected : d345124 q = 1) : d345124 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d345125 q = 1) : d349347 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d345125, d349347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d345125, d349347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d345126 q = 1) : d349348 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d345126, d349348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d345126, d349348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d345127 q = 1) : d349349 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d345127, d349349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d345127, d349349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d345128 q = 1) : d349350 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d345128, d349350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d345128, d349350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d345129 q = 1) : d349351 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d345129, d349351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d345129, d349351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro36527 (p : Pattern) (selected : d345135 p = 1) : d349357 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345130 q = 1) : d349352 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d345130, d349352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345130, d349352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36526 q selected
  have h2 (q : Pattern) (selected : d345131 q = 1) : d349353 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d345131, d349353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345131, d349353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d345132 q = 1) : d349354 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d345132, d349354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345132, d349354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d345133 q = 1) : d349355 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d345133, d349355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345133, d349355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d345134 q = 1) : d349356 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d345134, d349356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345134, d349356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d345135 q = 1) : d349357 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d345135, d349357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345135, d349357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro36528 (p : Pattern) (selected : d345292 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d203626 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19755 q selected
    | true =>
      simp only [d203626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203627 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d203627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d345286 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d345286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d345286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d345287 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d345287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d345288 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d345288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19757 q selected
    | true =>
      simp only [d345288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19790 q selected
  have h6 (q : Pattern) (selected : d345289 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d345289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d345289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d203642 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19760 q selected
    | true =>
      simp only [d203642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d203643 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d203643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d203643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d345290 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d345290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d345290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d345291 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d345291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d345291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d345292 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d345292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d345292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro36529 (p : Pattern) (selected : d345299 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d345288 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d345288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19757 q selected
    | true =>
      simp only [d345288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19790 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d345289 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d345289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203642 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19760 q selected
    | true =>
      simp only [d203642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d203643 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d203643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d345290 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d345290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d345290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d345291 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d345291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d345291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d345297 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d345297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d345297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d345298 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d345298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d345298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d345299 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d345299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d345299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro36530 (p : Pattern) (selected : d345309 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345305 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d345305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19757 q selected
    | true =>
      simp only [d345305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d345306 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d345306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d345306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d345307 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d345307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d345307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d345308 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d345308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203642 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19760 q selected
    | true =>
      simp only [d203642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d203643 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d203643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d345297 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d345297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d345297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d345298 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d345298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d345298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d345309 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d345309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d345309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro36531 (p : Pattern) (selected : d345316 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d203642 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19760 q selected
    | true =>
      simp only [d203642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d203643 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d203643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d203643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d345297 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d345297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d345297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d345298 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d345298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d203662 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19764 q selected
    | true =>
      simp only [d203662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d203663 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d203663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d203663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d345314 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d345314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d345314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d345315 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d345315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d345315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d345316 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d345316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d345316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro36532 (p : Pattern) (selected : d345322 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345293 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d345293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36528 q selected
    | true =>
      simp only [d345293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d345294 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d345294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d345294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d345295 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d345295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d345296 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d345296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d345300 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d345300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36529 q selected
    | true =>
      simp only [d345300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d345301 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d345301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d345301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d345302 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d345302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d345303 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d345303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d345303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d345304 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d345304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d345304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d345310 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d345310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36530 q selected
    | true =>
      simp only [d345310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d345311 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d345311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d345311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d345312 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d345312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d345313 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d345313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d345313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d345317 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d345317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36531 q selected
    | true =>
      simp only [d345317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d345318 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d345318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d345318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d345319 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d345319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d345320 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d345320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d345320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d345321 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d345321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d345321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d345322 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d345322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d345322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro36533 (p : Pattern) (selected : d345327 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d345288 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d345288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19757 q selected
    | true =>
      simp only [d345288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19790 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d345289 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d345289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203642 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19760 q selected
    | true =>
      simp only [d203642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d203643 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d203643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d345290 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d345290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d345290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d345291 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d345291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d345291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d345323 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d345323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19760 q selected
    | true =>
      simp only [d345323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19764 q selected
  have h8 (q : Pattern) (selected : d345324 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d345324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d345324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d203662 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19764 q selected
    | true =>
      simp only [d203662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h10 (q : Pattern) (selected : d203663 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d203663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d203663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h11 (q : Pattern) (selected : d345325 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d345325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d345325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d345326 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d345326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d345326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h13 (q : Pattern) (selected : d345327 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d345327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d345327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro36534 (p : Pattern) (selected : d345332 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d345323 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d345323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19760 q selected
    | true =>
      simp only [d345323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19764 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d345324 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d345324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d203662 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d203662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19764 q selected
    | true =>
      simp only [d203662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d203663 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d203663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d203663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d345325 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d345325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d345325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d345326 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d345326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d345326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d345314 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d345314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d345314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d345315 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d345315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d345315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d345332 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d345332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d345332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro36535 (p : Pattern) (selected : d345339 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345328 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d345328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36533 q selected
    | true =>
      simp only [d345328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d345329 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d345329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d345329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d345330 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d345330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d345331 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d345331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d345333 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d345333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36534 q selected
    | true =>
      simp only [d345333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d345334 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d345334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d345334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d345335 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d345335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d345336 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d345336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d345336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d345337 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d345337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d345337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d345317 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d345317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36531 q selected
    | true =>
      simp only [d345317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d345318 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d345318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d345318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d345319 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d345319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d345320 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d345320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d345320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d345338 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d345338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d345338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d345339 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d345339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d345339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro36536 (p : Pattern) (selected : d345344 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345333 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d345333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36534 q selected
    | true =>
      simp only [d345333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d345334 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d345334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d345334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d345335 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d345335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d345336 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d345336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d345343 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d345343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d345343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d345344 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d345344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d345344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36537 (p : Pattern) (selected : d345351 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345340 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d345340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36532 q selected
    | true =>
      simp only [d345340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36535 q selected
  have h2 (q : Pattern) (selected : d345341 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d345341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d345342 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d345342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d345345 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d345345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36535 q selected
    | true =>
      simp only [d345345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36536 q selected
  have h5 (q : Pattern) (selected : d345346 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d345346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d345347 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d345347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d345348 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d345348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d345349 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d345349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d345349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d345350 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d345350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d345350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d345351 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d345351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d345351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro36538 (p : Pattern) (selected : d345355 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345345 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d345345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36535 q selected
    | true =>
      simp only [d345345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36536 q selected
  have h2 (q : Pattern) (selected : d345346 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d345346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d345347 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d345347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d345349 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d345349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d345354 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d345354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d345354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d345355 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d345355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d345355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36539 (p : Pattern) (selected : d345361 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345352 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d345352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36537 q selected
    | true =>
      simp only [d345352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d345353 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d345353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d345356 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d345356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36538 q selected
    | true =>
      simp only [d345356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d345357 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d345357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d345358 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d345358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d345358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d345359 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d345359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d345359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d345360 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d345360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d345360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d345361 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d345361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro36540 (p : Pattern) (selected : d345365 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345356 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d345356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36538 q selected
    | true =>
      simp only [d345356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d345357 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d345357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d345362 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d345362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d345362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d345363 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d345363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d345364 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d345364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d345364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d345365 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d345365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro36541 (p : Pattern) (selected : d345377 p = 1) : d349365 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345243 q = 1) : d345243 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d345252 q = 1) : d345252 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d345285 q = 1) : d345285 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d345366 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d345366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36539 q selected
    | true =>
      simp only [d345366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36540 q selected
  have h5 (q : Pattern) (selected : d345367 q = 1) : d349361 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d345367, d349361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345367, d349361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d345373 q = 1) : d345373 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d345374 q = 1) : d349362 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d345374, d349362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d345374, d349362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d345375 q = 1) : d349363 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d345375, d349363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d345375, d349363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d345376 q = 1) : d349364 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d345376, d349364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d345376, d349364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d345377 q = 1) : d349365 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d345377, d349365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345377, d349365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro36542 (p : Pattern) (selected : d345391 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345352 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d345352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36537 q selected
    | true =>
      simp only [d345352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d345353 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d345353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d345356 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d345356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36538 q selected
    | true =>
      simp only [d345356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d345357 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d345357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d345358 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d345358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d345358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d345359 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d345359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d345359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d345360 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d345360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d345360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d345391 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d345391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d345391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro36543 (p : Pattern) (selected : d345392 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345356 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d345356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36538 q selected
    | true =>
      simp only [d345356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d345357 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d345357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d345362 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d345362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d345362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d345363 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d345363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d345364 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d345364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d345364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d345392 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d345392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d345392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36544 (p : Pattern) (selected : d345401 p = 1) : d349370 p = 1 := by
  have h0 (q : Pattern) (selected : d345243 q = 1) : d345243 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345252 q = 1) : d345252 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d345285 q = 1) : d345285 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d345366 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d345366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36539 q selected
    | true =>
      simp only [d345366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36540 q selected
  have h4 (q : Pattern) (selected : d345367 q = 1) : d349361 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d345367, d349361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d345367, d349361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d345373 q = 1) : d345373 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d345374 q = 1) : d349362 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d345374, d349362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d345374, d349362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d345375 q = 1) : d349363 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d345375, d349363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d345375, d349363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d345376 q = 1) : d349364 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d345376, d349364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345376, d349364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d345383 q = 1) : d345383 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d345388 q = 1) : d345388 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d345390 q = 1) : d345390 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d345393 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d345393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36542 q selected
    | true =>
      simp only [d345393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36543 q selected
  have h13 (q : Pattern) (selected : d345394 q = 1) : d349366 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d345394, d349366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d345394, d349366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d345397 q = 1) : d345397 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d345398 q = 1) : d349367 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d345398, d349367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d345398, d349367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d345399 q = 1) : d349368 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d345399, d349368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d345399, d349368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d345400 q = 1) : d349369 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d345400, d349369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d345400, d349369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d345401 q = 1) : d349370 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d345401, d349370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d345401, d349370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro36545 (p : Pattern) (selected : d345421 p = 1) : d349377 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345390 q = 1) : d345390 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d345393 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d345393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36542 q selected
    | true =>
      simp only [d345393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36543 q selected
  have h3 (q : Pattern) (selected : d345394 q = 1) : d349366 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d345394, d349366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d345394, d349366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d345397 q = 1) : d345397 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d345398 q = 1) : d349367 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d345398, d349367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345398, d349367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d345419 q = 1) : d349375 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d345419, d349375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345419, d349375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d345420 q = 1) : d349376 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d345420, d349376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345420, d349376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d345421 q = 1) : d349377 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d345421, d349377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345421, d349377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro36546 (p : Pattern) (selected : d345528 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345510 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d345510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36528 q selected
  have h2 (q : Pattern) (selected : d345293 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d345293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36528 q selected
    | true =>
      simp only [d345293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d345511 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d345511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d345511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d345294 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d345294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d345294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d345512 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d345512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d345513 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d345513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d345513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d345514 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d345514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36529 q selected
  have h8 (q : Pattern) (selected : d345300 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d345300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36529 q selected
    | true =>
      simp only [d345300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d345515 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d345515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d345515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d345301 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d345301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d345301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d345516 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d345516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d345516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d345517 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d345517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d345517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d345518 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d345518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d345518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d345519 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d345519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36530 q selected
  have h15 (q : Pattern) (selected : d345310 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d345310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36530 q selected
    | true =>
      simp only [d345310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d345520 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d345520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d345520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d345311 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d345311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d345311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d345521 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d345521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d345521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d345522 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d345522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d345522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d345523 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d345523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36531 q selected
  have h21 (q : Pattern) (selected : d345317 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d345317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36531 q selected
    | true =>
      simp only [d345317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d345524 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d345524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d345524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d345318 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d345318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d345318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d345525 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d345525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d345525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d345526 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d345526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d345526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d345527 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d345527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d345527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d345528 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d345528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d345528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro36547 (p : Pattern) (selected : d345539 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345529 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d345529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36533 q selected
  have h2 (q : Pattern) (selected : d345328 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d345328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36533 q selected
    | true =>
      simp only [d345328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d345530 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d345530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d345530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d345329 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d345329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d345329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d345531 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d345531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d345532 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d345532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d345532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d345533 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d345533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36534 q selected
  have h8 (q : Pattern) (selected : d345333 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d345333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36534 q selected
    | true =>
      simp only [d345333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d345534 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d345534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d345534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d345334 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d345334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d345334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d345535 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d345535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d345535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d345536 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d345536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d345536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d345537 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d345537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d345537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d345523 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d345523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36531 q selected
  have h15 (q : Pattern) (selected : d345317 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d345317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36531 q selected
    | true =>
      simp only [d345317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d345524 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d345524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d345524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d345318 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d345318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d345318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d345525 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d345525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d345525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d345526 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d345526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d345526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d345538 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d345538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d345538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d345539 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d345539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d345539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro36548 (p : Pattern) (selected : d345544 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345533 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d345533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36534 q selected
  have h2 (q : Pattern) (selected : d345333 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d345333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36534 q selected
    | true =>
      simp only [d345333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d345534 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d345534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d345534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d345334 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d345334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d345334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d345535 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d345535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d345536 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d345536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d345536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d345543 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d345543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d345543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d345544 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d345544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d345544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro36549 (p : Pattern) (selected : d345551 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345540 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d345540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36546 q selected
    | true =>
      simp only [d345540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36547 q selected
  have h2 (q : Pattern) (selected : d345541 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d345541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d345542 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d345542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d345545 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d345545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36547 q selected
    | true =>
      simp only [d345545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36548 q selected
  have h5 (q : Pattern) (selected : d345546 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d345546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d345547 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d345547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d345548 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d345548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d345549 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d345549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d345549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d345550 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d345550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d345550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d345551 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d345551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d345551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro36550 (p : Pattern) (selected : d345555 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345545 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d345545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36547 q selected
    | true =>
      simp only [d345545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36548 q selected
  have h2 (q : Pattern) (selected : d345546 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d345546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d345547 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d345547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d345549 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d345549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d345554 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d345554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d345554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d345555 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d345555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d345555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36551 (p : Pattern) (selected : d345561 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345552 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d345552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36549 q selected
    | true =>
      simp only [d345552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d345553 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d345553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d345556 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d345556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36550 q selected
    | true =>
      simp only [d345556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d345557 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d345557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d345558 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d345558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d345558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d345559 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d345559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d345559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d345560 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d345560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d345560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d345561 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d345561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d345561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro36552 (p : Pattern) (selected : d345565 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345556 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d345556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36550 q selected
    | true =>
      simp only [d345556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d345557 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d345557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d345562 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d345562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d345562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d345563 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d345563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d345564 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d345564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d345564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d345565 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d345565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d345565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36553 (p : Pattern) (selected : d345577 p = 1) : d349387 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345509 q = 1) : d345509 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d345566 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d345566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36551 q selected
    | true =>
      simp only [d345566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36552 q selected
  have h3 (q : Pattern) (selected : d345567 q = 1) : d349383 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d345567, d349383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d345567, d349383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d345573 q = 1) : d345573 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d345574 q = 1) : d349384 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d345574, d349384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345574, d349384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d345575 q = 1) : d349385 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d345575, d349385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345575, d349385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d345576 q = 1) : d349386 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d345576, d349386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345576, d349386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d345577 q = 1) : d349387 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d345577, d349387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345577, d349387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro36554 (p : Pattern) (selected : d345594 p = 1) : d349393 p = 1 := by
  have h0 (q : Pattern) (selected : d345235 q = 1) : d345235 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345402 q = 1) : d349371 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d345402, d349371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36541 q selected
    | true =>
      simp only [d345402, d349371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36544 q selected
  have h2 (q : Pattern) (selected : d345415 q = 1) : d345415 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d345416 q = 1) : d349372 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d345416, d349372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d345416, d349372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d345417 q = 1) : d349373 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d345417, d349373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345417, d349373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d345418 q = 1) : d349374 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d345418, d349374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345418, d349374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d345422 q = 1) : d349378 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d345422, d349378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d345422, d349378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36545 q selected
  have h8 (q : Pattern) (selected : d345424 q = 1) : d345424 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d345425 q = 1) : d349379 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d345425, d349379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d345425, d349379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d345426 q = 1) : d349380 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d345426, d349380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d345426, d349380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d345427 q = 1) : d349381 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d345427, d349381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d345427, d349381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d345428 q = 1) : d349382 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d345428, d349382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d345428, d349382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d345578 q = 1) : d349388 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d345578, d349388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d345578, d349388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36553 q selected
  have h14 (q : Pattern) (selected : d345589 q = 1) : d345589 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d345590 q = 1) : d349389 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d345590, d349389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d345590, d349389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d345591 q = 1) : d349390 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d345591, d349390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d345591, d349390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d345592 q = 1) : d349391 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d345592, d349391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d345592, d349391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d345593 q = 1) : d349392 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d345593, d349392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d345593, d349392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d345594 q = 1) : d349393 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d345594, d349393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d345594, d349393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro36555 (p : Pattern) (selected : d345600 p = 1) : d349399 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345595 q = 1) : d349394 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d345595, d349394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345595, d349394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36554 q selected
  have h2 (q : Pattern) (selected : d345596 q = 1) : d349395 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d345596, d349395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345596, d349395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d345597 q = 1) : d349396 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d345597, d349396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345597, d349396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d345598 q = 1) : d349397 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d345598, d349397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345598, d349397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d345599 q = 1) : d349398 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d345599, d349398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345599, d349398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d345600 q = 1) : d349399 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d345600, d349399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345600, d349399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro36556 (p : Pattern) (selected : d345735 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345731 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d345731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19788 q selected
    | true =>
      simp only [d345731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d345732 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d345732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d345732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d345733 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d345733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d345733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d345734 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d345734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d345735 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d345735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro36557 (p : Pattern) (selected : d345744 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345731 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d345731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19788 q selected
    | true =>
      simp only [d345731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d345732 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d345732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d345732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d345733 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d345733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d345733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d345734 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d345734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d345740 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d345740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19792 q selected
    | true =>
      simp only [d345740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d345741 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d345741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d345741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d345742 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d345742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d345742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d345743 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d345743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d345743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d345744 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d345744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d345744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro36558 (p : Pattern) (selected : d345752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345740 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d345740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19792 q selected
    | true =>
      simp only [d345740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d345741 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d345741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d345741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d345742 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d345742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d345742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d345743 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d345743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d204070 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d204070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19798 q selected
    | true =>
      simp only [d204070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d204071 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d204071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d204071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d345750 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d345750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d345750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d345751 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d345751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d345751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d345752 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d345752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d345752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro36559 (p : Pattern) (selected : d345758 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345736 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d345736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36556 q selected
    | true =>
      simp only [d345736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d345737 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d345737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d345737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d345738 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d345738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d345739 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d345739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d345745 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d345745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36557 q selected
    | true =>
      simp only [d345745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d345746 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d345746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d345746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d345747 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d345747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d345748 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d345748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d345748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d345749 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d345749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d345749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d345753 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d345753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36558 q selected
    | true =>
      simp only [d345753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d345754 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d345754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d345754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d345755 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d345755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d345756 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d345756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d345756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d345757 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d345757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d345757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d345758 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d345758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d345758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro36560 (p : Pattern) (selected : d345763 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345731 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d345731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19788 q selected
    | true =>
      simp only [d345731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d345732 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d345732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d345732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d345733 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d345733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d345733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d345734 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d345734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d345759 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d345759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19792 q selected
    | true =>
      simp only [d345759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19798 q selected
  have h6 (q : Pattern) (selected : d345760 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d345760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d345760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d204070 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d204070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19798 q selected
    | true =>
      simp only [d204070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d204071 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d204071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d204071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d345761 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d345761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d345761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d345762 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d345762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d345762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d345763 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d345763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d345763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro36561 (p : Pattern) (selected : d345768 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d345759 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d345759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19792 q selected
    | true =>
      simp only [d345759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19798 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d345760 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d345760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d204070 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d204070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19798 q selected
    | true =>
      simp only [d204070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d204071 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d204071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d204071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d345761 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d345761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d345761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d345762 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d345762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d345762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d345750 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d345750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d345750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d345751 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d345751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d345751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d345768 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d345768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d345768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro36562 (p : Pattern) (selected : d345775 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345764 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d345764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36560 q selected
    | true =>
      simp only [d345764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d345765 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d345765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d345765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d345766 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d345766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d345767 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d345767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d345769 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d345769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36561 q selected
    | true =>
      simp only [d345769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d345770 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d345770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d345770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d345771 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d345771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d345772 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d345772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d345772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d345773 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d345773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d345773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d345753 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d345753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36558 q selected
    | true =>
      simp only [d345753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d345754 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d345754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d345754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d345755 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d345755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d345756 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d345756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d345756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d345774 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d345774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d345774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d345775 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d345775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d345775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro36563 (p : Pattern) (selected : d345780 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345769 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d345769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36561 q selected
    | true =>
      simp only [d345769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d345770 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d345770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d345770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d345771 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d345771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d345772 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d345772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d345779 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d345779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d345779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d345780 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d345780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d345780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36564 (p : Pattern) (selected : d345787 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345776 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d345776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36559 q selected
    | true =>
      simp only [d345776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36562 q selected
  have h2 (q : Pattern) (selected : d345777 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d345777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d345778 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d345778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d345781 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d345781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36562 q selected
    | true =>
      simp only [d345781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36563 q selected
  have h5 (q : Pattern) (selected : d345782 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d345782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d345783 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d345783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d345784 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d345784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d345785 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d345785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d345785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d345786 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d345786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d345786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d345787 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d345787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d345787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro36565 (p : Pattern) (selected : d345791 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345781 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d345781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36562 q selected
    | true =>
      simp only [d345781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36563 q selected
  have h2 (q : Pattern) (selected : d345782 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d345782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d345783 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d345783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d345785 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d345785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d345790 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d345790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d345790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d345791 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d345791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d345791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36566 (p : Pattern) (selected : d345797 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345788 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d345788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36564 q selected
    | true =>
      simp only [d345788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d345789 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d345789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d345792 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d345792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36565 q selected
    | true =>
      simp only [d345792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d345793 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d345793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d345794 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d345794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d345794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d345795 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d345795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d345795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d345796 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d345796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d345796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d345797 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d345797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro36567 (p : Pattern) (selected : d345801 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345792 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d345792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36565 q selected
    | true =>
      simp only [d345792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d345793 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d345793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d345798 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d345798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d345798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d345799 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d345799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d345800 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d345800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d345800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d345801 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d345801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro36568 (p : Pattern) (selected : d345839 p = 1) : d349408 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345702 q = 1) : d345702 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d345711 q = 1) : d345711 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d345730 q = 1) : d345730 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d345802 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d345802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36566 q selected
    | true =>
      simp only [d345802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36567 q selected
  have h5 (q : Pattern) (selected : d345803 q = 1) : d349404 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d345803, d349404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345803, d349404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d345835 q = 1) : d345835 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d345836 q = 1) : d349405 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d345836, d349405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d345836, d349405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d345837 q = 1) : d349406 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d345837, d349406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d345837, d349406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d345838 q = 1) : d349407 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d345838, d349407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d345838, d349407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d345839 q = 1) : d349408 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d345839, d349408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345839, d349408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro36569 (p : Pattern) (selected : d345853 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345788 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d345788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36564 q selected
    | true =>
      simp only [d345788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d345789 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d345789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d345792 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d345792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36565 q selected
    | true =>
      simp only [d345792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d345793 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d345793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d345794 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d345794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d345794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d345795 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d345795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d345795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d345796 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d345796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d345796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d345853 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d345853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d345853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro36570 (p : Pattern) (selected : d345854 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345792 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d345792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36565 q selected
    | true =>
      simp only [d345792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d345793 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d345793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d345798 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d345798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d345798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d345799 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d345799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d345800 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d345800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d345800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d345854 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d345854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d345854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36571 (p : Pattern) (selected : d345863 p = 1) : d349413 p = 1 := by
  have h0 (q : Pattern) (selected : d345702 q = 1) : d345702 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345711 q = 1) : d345711 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d345730 q = 1) : d345730 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d345802 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d345802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36566 q selected
    | true =>
      simp only [d345802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36567 q selected
  have h4 (q : Pattern) (selected : d345803 q = 1) : d349404 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d345803, d349404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d345803, d349404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d345835 q = 1) : d345835 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d345836 q = 1) : d349405 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d345836, d349405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d345836, d349405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d345837 q = 1) : d349406 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d345837, d349406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d345837, d349406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d345838 q = 1) : d349407 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d345838, d349407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345838, d349407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d345845 q = 1) : d345845 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d345850 q = 1) : d345850 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d345852 q = 1) : d345852 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d345855 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d345855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36569 q selected
    | true =>
      simp only [d345855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36570 q selected
  have h13 (q : Pattern) (selected : d345856 q = 1) : d349409 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d345856, d349409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d345856, d349409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d345859 q = 1) : d345859 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d345860 q = 1) : d349410 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d345860, d349410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d345860, d349410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d345861 q = 1) : d349411 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d345861, d349411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d345861, d349411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d345862 q = 1) : d349412 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d345862, d349412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d345862, d349412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d345863 q = 1) : d349413 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d345863, d349413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d345863, d349413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro36572 (p : Pattern) (selected : d345883 p = 1) : d349420 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345852 q = 1) : d345852 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d345855 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d345855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36569 q selected
    | true =>
      simp only [d345855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36570 q selected
  have h3 (q : Pattern) (selected : d345856 q = 1) : d349409 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d345856, d349409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d345856, d349409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d345859 q = 1) : d345859 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d345860 q = 1) : d349410 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d345860, d349410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345860, d349410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d345881 q = 1) : d349418 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d345881, d349418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345881, d349418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d345882 q = 1) : d349419 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d345882, d349419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345882, d349419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d345883 q = 1) : d349420 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d345883, d349420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345883, d349420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro36573 (p : Pattern) (selected : d345972 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345958 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d345958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36556 q selected
  have h2 (q : Pattern) (selected : d345736 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d345736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36556 q selected
    | true =>
      simp only [d345736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d345959 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d345959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d345959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d345737 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d345737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d345737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d345960 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d345960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d345961 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d345961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d345961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d345962 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d345962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36557 q selected
  have h8 (q : Pattern) (selected : d345745 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d345745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36557 q selected
    | true =>
      simp only [d345745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d345963 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d345963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d345963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d345746 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d345746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d345746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d345964 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d345964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d345964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d345965 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d345965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d345965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d345966 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d345966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d345966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d345967 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d345967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36558 q selected
  have h15 (q : Pattern) (selected : d345753 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d345753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36558 q selected
    | true =>
      simp only [d345753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d345968 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d345968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d345968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d345754 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d345754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d345754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d345969 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d345969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d345969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d345970 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d345970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d345970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d345971 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d345971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d345971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d345972 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d345972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d345972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro36574 (p : Pattern) (selected : d345983 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345973 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d345973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36560 q selected
  have h2 (q : Pattern) (selected : d345764 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d345764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36560 q selected
    | true =>
      simp only [d345764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d345974 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d345974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d345974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d345765 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d345765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d345765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d345975 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d345975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d345976 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d345976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d345976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d345977 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d345977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36561 q selected
  have h8 (q : Pattern) (selected : d345769 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d345769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36561 q selected
    | true =>
      simp only [d345769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d345978 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d345978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d345978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d345770 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d345770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d345770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d345979 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d345979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d345979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d345980 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d345980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d345980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d345981 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d345981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d345981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d345967 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d345967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36558 q selected
  have h15 (q : Pattern) (selected : d345753 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d345753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36558 q selected
    | true =>
      simp only [d345753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d345968 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d345968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d345968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d345754 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d345754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d345754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d345969 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d345969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d345969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d345970 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d345970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d345970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d345982 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d345982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d345982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d345983 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d345983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d345983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro36575 (p : Pattern) (selected : d345988 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345977 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d345977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36561 q selected
  have h2 (q : Pattern) (selected : d345769 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d345769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36561 q selected
    | true =>
      simp only [d345769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d345978 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d345978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d345978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d345770 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d345770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d345770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d345979 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d345979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d345980 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d345980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d345980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d345987 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d345987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d345987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d345988 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d345988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d345988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro36576 (p : Pattern) (selected : d345995 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345984 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d345984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36573 q selected
    | true =>
      simp only [d345984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36574 q selected
  have h2 (q : Pattern) (selected : d345985 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d345985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d345986 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d345986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d345989 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d345989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36574 q selected
    | true =>
      simp only [d345989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36575 q selected
  have h5 (q : Pattern) (selected : d345990 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d345990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d345991 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d345991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d345992 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d345992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d345993 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d345993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d345993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d345994 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d345994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d345994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d345995 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d345995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d345995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro36577 (p : Pattern) (selected : d345999 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345989 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d345989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36574 q selected
    | true =>
      simp only [d345989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36575 q selected
  have h2 (q : Pattern) (selected : d345990 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d345990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d345991 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d345991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d345993 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d345993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d345998 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d345998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d345998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d345999 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d345999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d345999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36578 (p : Pattern) (selected : d346005 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345996 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d345996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36576 q selected
    | true =>
      simp only [d345996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d345997 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d345997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d346000 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d346000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36577 q selected
    | true =>
      simp only [d346000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d346001 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d346001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d346001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d346002 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d346002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d346002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d346003 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d346003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d346003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d346004 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d346004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d346004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d346005 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d346005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d346005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro36579 (p : Pattern) (selected : d346009 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d346000 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d346000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36577 q selected
    | true =>
      simp only [d346000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d346001 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d346001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d346001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d346006 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d346006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d346006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d346007 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d346007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d346007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d346008 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d346008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d346008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d346009 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d346009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d346009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36580 (p : Pattern) (selected : d346041 p = 1) : d349430 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345957 q = 1) : d345957 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d346010 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d346010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36578 q selected
    | true =>
      simp only [d346010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36579 q selected
  have h3 (q : Pattern) (selected : d346011 q = 1) : d349426 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d346011, d349426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d346011, d349426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d346037 q = 1) : d346037 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d346038 q = 1) : d349427 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d346038, d349427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d346038, d349427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d346039 q = 1) : d349428 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d346039, d349428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d346039, d349428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d346040 q = 1) : d349429 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d346040, d349429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d346040, d349429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d346041 q = 1) : d349430 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d346041, d349430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d346041, d349430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro36581 (p : Pattern) (selected : d346058 p = 1) : d349436 p = 1 := by
  have h0 (q : Pattern) (selected : d345694 q = 1) : d345694 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d345864 q = 1) : d349414 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d345864, d349414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36568 q selected
    | true =>
      simp only [d345864, d349414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36571 q selected
  have h2 (q : Pattern) (selected : d345877 q = 1) : d345877 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d345878 q = 1) : d349415 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d345878, d349415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d345878, d349415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d345879 q = 1) : d349416 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d345879, d349416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345879, d349416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d345880 q = 1) : d349417 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d345880, d349417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d345880, d349417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d345884 q = 1) : d349421 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d345884, d349421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d345884, d349421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36572 q selected
  have h8 (q : Pattern) (selected : d345886 q = 1) : d345886 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d345887 q = 1) : d349422 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d345887, d349422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d345887, d349422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d345888 q = 1) : d349423 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d345888, d349423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d345888, d349423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d345889 q = 1) : d349424 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d345889, d349424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d345889, d349424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d345890 q = 1) : d349425 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d345890, d349425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d345890, d349425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d346042 q = 1) : d349431 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d346042, d349431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d346042, d349431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36580 q selected
  have h14 (q : Pattern) (selected : d346053 q = 1) : d346053 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d346054 q = 1) : d349432 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d346054, d349432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d346054, d349432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d346055 q = 1) : d349433 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d346055, d349433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d346055, d349433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d346056 q = 1) : d349434 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d346056, d349434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d346056, d349434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d346057 q = 1) : d349435 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d346057, d349435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d346057, d349435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d346058 q = 1) : d349436 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d346058, d349436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d346058, d349436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro36582 (p : Pattern) (selected : d346064 p = 1) : d349442 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d346059 q = 1) : d349437 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d346059, d349437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d346059, d349437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36581 q selected
  have h2 (q : Pattern) (selected : d346060 q = 1) : d349438 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d346060, d349438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d346060, d349438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d346061 q = 1) : d349439 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d346061, d349439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d346061, d349439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d346062 q = 1) : d349440 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d346062, d349440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d346062, d349440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d346063 q = 1) : d349441 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d346063, d349441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d346063, d349441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d346064 q = 1) : d349442 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d346064, d349442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d346064, d349442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro36583 (p : Pattern) (selected : d346070 p = 1) : d349448 p = 1 := by
  have h0 (q : Pattern) (selected : d344513 q = 1) : d349277 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d344513, d349277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19689 q selected
    | true =>
      simp only [d344513, d349277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36486 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d344715 q = 1) : d349317 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d344715, d349317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d344715, d349317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36500 q selected
  have h3 (q : Pattern) (selected : d344716 q = 1) : d349318 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d344716, d349318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d344716, d349318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d345136 q = 1) : d349358 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d345136, d349358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d345136, d349358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36527 q selected
  have h5 (q : Pattern) (selected : d345137 q = 1) : d349359 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d345137, d349359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d345137, d349359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d345138 q = 1) : d349360 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d345138, d349360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345138, d349360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d345601 q = 1) : d349400 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d345601, d349400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d345601, d349400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36555 q selected
  have h8 (q : Pattern) (selected : d345602 q = 1) : d349401 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d345602, d349401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d345602, d349401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d345603 q = 1) : d349402 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d345603, d349402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d345603, d349402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d345604 q = 1) : d349403 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d345604, d349403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d345604, d349403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d346065 q = 1) : d349443 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d346065, d349443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d346065, d349443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36582 q selected
  have h12 (q : Pattern) (selected : d346066 q = 1) : d349444 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d346066, d349444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d346066, d349444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d346067 q = 1) : d349445 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d346067, d349445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d346067, d349445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d346068 q = 1) : d349446 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d346068, d349446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d346068, d349446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d346069 q = 1) : d349447 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d346069, d349447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d346069, d349447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d346070 q = 1) : d349448 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d346070, d349448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d346070, d349448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro36584 (p : Pattern) (selected : d346076 p = 1) : d349454 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d346071 q = 1) : d349449 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d346071, d349449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36583 q selected
    | true =>
      simp only [d346071, d349449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d346072 q = 1) : d349450 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d346072, d349450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d346072, d349450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d346073 q = 1) : d349451 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d346073, d349451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d346073, d349451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d346074 q = 1) : d349452 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d346074, d349452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d346074, d349452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d346075 q = 1) : d349453 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d346075, d349453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d346075, d349453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d346076 q = 1) : d349454 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d346076, d349454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d346076, d349454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36585 (p : Pattern) (selected : d346082 p = 1) : d349460 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d346077 q = 1) : d349455 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d346077, d349455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36584 q selected
    | true =>
      simp only [d346077, d349455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d346078 q = 1) : d349456 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d346078, d349456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d346078, d349456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d346079 q = 1) : d349457 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d346079, d349457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d346079, d349457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d346080 q = 1) : d349458 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d346080, d349458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d346080, d349458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d346081 q = 1) : d349459 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d346081, d349459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d346081, d349459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d346082 q = 1) : d349460 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d346082, d349460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d346082, d349460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36586 (p : Pattern) (selected : d346088 p = 1) : d349466 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d346083 q = 1) : d349461 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d346083, d349461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36585 q selected
    | true =>
      simp only [d346083, d349461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d346084 q = 1) : d349462 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d346084, d349462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d346084, d349462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d346085 q = 1) : d349463 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d346085, d349463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d346085, d349463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d346086 q = 1) : d349464 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d346086, d349464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d346086, d349464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d346087 q = 1) : d349465 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d346087, d349465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d346087, d349465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d346088 q = 1) : d349466 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d346088, d349466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d346088, d349466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36587 (p : Pattern) (selected : d346094 p = 1) : d349472 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d346089 q = 1) : d349467 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d346089, d349467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36586 q selected
    | true =>
      simp only [d346089, d349467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d346090 q = 1) : d349468 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d346090, d349468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d346090, d349468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d346091 q = 1) : d349469 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d346091, d349469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d346091, d349469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d346092 q = 1) : d349470 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d346092, d349470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d346092, d349470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d346093 q = 1) : d349471 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d346093, d349471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d346093, d349471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d346094 q = 1) : d349472 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d346094, d349472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d346094, d349472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36588 (p : Pattern) (selected : d346100 p = 1) : d349478 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d346095 q = 1) : d349473 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d346095, d349473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36587 q selected
    | true =>
      simp only [d346095, d349473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d346096 q = 1) : d349474 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d346096, d349474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d346096, d349474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d346097 q = 1) : d349475 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d346097, d349475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d346097, d349475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d346098 q = 1) : d349476 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d346098, d349476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d346098, d349476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d346099 q = 1) : d349477 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d346099, d349477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d346099, d349477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d346100 q = 1) : d349478 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d346100, d349478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d346100, d349478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36589 (p : Pattern) (selected : d346106 p = 1) : d349484 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d346101 q = 1) : d349479 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d346101, d349479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36588 q selected
    | true =>
      simp only [d346101, d349479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d346102 q = 1) : d349480 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d346102, d349480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d346102, d349480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d346103 q = 1) : d349481 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d346103, d349481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d346103, d349481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d346104 q = 1) : d349482 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d346104, d349482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d346104, d349482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d346105 q = 1) : d349483 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d346105, d349483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d346105, d349483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d346106 q = 1) : d349484 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d346106, d349484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d346106, d349484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36590 (p : Pattern) (selected : d346112 p = 1) : d349490 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d346107 q = 1) : d349485 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d346107, d349485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36589 q selected
    | true =>
      simp only [d346107, d349485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d346108 q = 1) : d349486 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d346108, d349486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d346108, d349486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d346109 q = 1) : d349487 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d346109, d349487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d346109, d349487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d346110 q = 1) : d349488 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d346110, d349488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d346110, d349488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d346111 q = 1) : d349489 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d346111, d349489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d346111, d349489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d346112 q = 1) : d349490 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d346112, d349490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d346112, d349490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36591 (p : Pattern) (selected : d351903 p = 0) : d354135 p = 1 := by
  have h0 (q : Pattern) (selected : d1 q = 0) : d0 q = 1 := by
    change (1 : Int) = 0 at selected
    omega
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d253269 q = 0) : d253268 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d253269, d253268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253269, d253268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d351901 q = 0) : d354133 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d351901, d354133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d351901, d354133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d351902 q = 0) : d354134 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d351902, d354134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d351902, d354134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d351903 q = 0) : d354135 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d351903, d354135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d351903, d354135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h5 p selected
theorem eqIntro36592 (p : Pattern) (selected : d351909 p = 0) : d354141 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d351904 q = 0) : d354136 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d351904, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36591 q selected
    | true =>
      simp only [d351904, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d351905 q = 0) : d354137 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d351905, d354137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d351905, d354137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d351906 q = 0) : d354138 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d351906, d354138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d351906, d354138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d351907 q = 0) : d354139 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d351907, d354139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d351907, d354139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d351908 q = 0) : d354140 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d351908, d354140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d351908, d354140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d351909 q = 0) : d354141 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d351909, d354141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d351909, d354141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36593 (p : Pattern) (selected : d351915 p = 0) : d354147 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d351910 q = 0) : d354142 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d351910, d354142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36592 q selected
    | true =>
      simp only [d351910, d354142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d351911 q = 0) : d354143 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d351911, d354143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d351911, d354143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d351912 q = 0) : d354144 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d351912, d354144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351912, d354144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d351913 q = 0) : d354145 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d351913, d354145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d351913, d354145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d351914 q = 0) : d354146 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d351914, d354146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d351914, d354146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d351915 q = 0) : d354147 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d351915, d354147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d351915, d354147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36594 (p : Pattern) (selected : d351921 p = 0) : d354153 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d351916 q = 0) : d354148 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d351916, d354148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36593 q selected
    | true =>
      simp only [d351916, d354148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d351917 q = 0) : d354149 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d351917, d354149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351917, d354149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d351918 q = 0) : d354150 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d351918, d354150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351918, d354150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d351919 q = 0) : d354151 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d351919, d354151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d351919, d354151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d351920 q = 0) : d354152 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d351920, d354152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d351920, d354152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d351921 q = 0) : d354153 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d351921, d354153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d351921, d354153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36595 (p : Pattern) (selected : d351927 p = 0) : d354159 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d351922 q = 0) : d354154 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d351922, d354154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36594 q selected
    | true =>
      simp only [d351922, d354154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d351923 q = 0) : d354155 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d351923, d354155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351923, d354155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d351924 q = 0) : d354156 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d351924, d354156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d351924, d354156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d351925 q = 0) : d354157 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d351925, d354157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d351925, d354157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d351926 q = 0) : d354158 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d351926, d354158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d351926, d354158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d351927 q = 0) : d354159 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d351927, d354159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351927, d354159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro36596 (p : Pattern) (selected : d351933 p = 0) : d354165 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d351928 q = 0) : d354160 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d351928, d354160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36595 q selected
    | true =>
      simp only [d351928, d354160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d351929 q = 0) : d354161 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d351929, d354161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d351929, d354161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d351930 q = 0) : d354162 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d351930, d354162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d351930, d354162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d351931 q = 0) : d354163 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d351931, d354163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351931, d354163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d351932 q = 0) : d354164 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d351932, d354164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351932, d354164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d351933 q = 0) : d354165 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d351933, d354165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351933, d354165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro36597 (p : Pattern) (selected : d351934 p = 0) : d354166 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d351922 q = 0) : d354154 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d351922, d354154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36594 q selected
    | true =>
      simp only [d351922, d354154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d351923 q = 0) : d354155 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d351923, d354155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351923, d354155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d351924 q = 0) : d354156 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d351924, d354156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d351924, d354156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d351925 q = 0) : d354157 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d351925, d354157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d351925, d354157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d351926 q = 0) : d354158 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d351926, d354158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d351926, d354158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d351934 q = 0) : d354166 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d351934, d354166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d351934, d354166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36598 (p : Pattern) (selected : d351940 p = 0) : d354172 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d351928 q = 0) : d354160 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d351928, d354160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36595 q selected
    | true =>
      simp only [d351928, d354160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d351929 q = 0) : d354161 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d351929, d354161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d351929, d354161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d351930 q = 0) : d354162 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d351930, d354162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d351930, d354162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d351931 q = 0) : d354163 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d351931, d354163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351931, d354163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d351932 q = 0) : d354164 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d351932, d354164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351932, d354164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d351935 q = 0) : d354167 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d351935, d354167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36597 q selected
    | true =>
      simp only [d351935, d354167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d351936 q = 0) : d354168 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d351936, d354168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d351936, d354168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d351937 q = 0) : d354169 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d351937, d354169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d351937, d354169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d351938 q = 0) : d354170 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d351938, d354170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351938, d354170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d351939 q = 0) : d354171 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d351939, d354171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351939, d354171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d351940 q = 0) : d354172 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d351940, d354172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d351940, d354172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro36599 (p : Pattern) (selected : d351945 p = 0) : d354177 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d351935 q = 0) : d354167 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d351935, d354167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36597 q selected
    | true =>
      simp only [d351935, d354167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d351936 q = 0) : d354168 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d351936, d354168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d351936, d354168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d351937 q = 0) : d354169 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d351937, d354169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d351937, d354169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d351938 q = 0) : d354170 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d351938, d354170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351938, d354170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d351939 q = 0) : d354171 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d351939, d354171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351939, d354171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d351945 q = 0) : d354177 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d351945, d354177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351945, d354177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro36600 (p : Pattern) (selected : d351956 p = 0) : d354188 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d351951 q = 0) : d354183 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d351951, d354183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351951, d354183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36592 q selected
  have h2 (q : Pattern) (selected : d351910 q = 0) : d354142 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d351910, d354142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36592 q selected
    | true =>
      simp only [d351910, d354142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d351952 q = 0) : d354184 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d351952, d354184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d351952, d354184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d351911 q = 0) : d354143 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d351911, d354143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d351911, d354143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d351953 q = 0) : d354185 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d351953, d354185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d351953, d354185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d351954 q = 0) : d354186 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d351954, d354186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d351954, d354186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d351955 q = 0) : d354187 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d351955, d354187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d351955, d354187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d351956 q = 0) : d354188 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d351956, d354188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d351956, d354188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro36601 (p : Pattern) (selected : d351962 p = 0) : d354194 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d351957 q = 0) : d354189 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d351957, d354189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36600 q selected
    | true =>
      simp only [d351957, d354189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d351958 q = 0) : d354190 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d351958, d354190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351958, d354190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d351959 q = 0) : d354191 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d351959, d354191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351959, d354191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d351960 q = 0) : d354192 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d351960, d354192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d351960, d354192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d351961 q = 0) : d354193 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d351961, d354193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d351961, d354193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d351962 q = 0) : d354194 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d351962, d354194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d351962, d354194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36602 (p : Pattern) (selected : d351968 p = 0) : d354200 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d351963 q = 0) : d354195 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d351963, d354195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36601 q selected
    | true =>
      simp only [d351963, d354195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d351964 q = 0) : d354196 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d351964, d354196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351964, d354196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d351965 q = 0) : d354197 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d351965, d354197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d351965, d354197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d351966 q = 0) : d354198 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d351966, d354198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d351966, d354198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d351967 q = 0) : d354199 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d351967, d354199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d351967, d354199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d351968 q = 0) : d354200 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d351968, d354200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d351968, d354200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36603 (p : Pattern) (selected : d351974 p = 0) : d354206 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d351969 q = 0) : d354201 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d351969, d354201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36602 q selected
    | true =>
      simp only [d351969, d354201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d351970 q = 0) : d354202 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d351970, d354202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d351970, d354202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d351971 q = 0) : d354203 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d351971, d354203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d351971, d354203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d351972 q = 0) : d354204 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d351972, d354204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351972, d354204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d351973 q = 0) : d354205 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d351973, d354205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351973, d354205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d351974 q = 0) : d354206 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d351974, d354206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351974, d354206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro36604 (p : Pattern) (selected : d351980 p = 0) : d354212 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d351941 q = 0) : d354173 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d351941, d354173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36596 q selected
    | true =>
      simp only [d351941, d354173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36598 q selected
  have h2 (q : Pattern) (selected : d351942 q = 0) : d354174 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d351942, d354174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d351942, d354174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d351943 q = 0) : d354175 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d351943, d354175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d351943, d354175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d351944 q = 0) : d354176 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d351944, d354176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351944, d354176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d351946 q = 0) : d354178 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d351946, d354178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351946, d354178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36599 q selected
  have h6 (q : Pattern) (selected : d351947 q = 0) : d354179 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d351947, d354179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d351947, d354179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d351948 q = 0) : d354180 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d351948, d354180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d351948, d354180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d351949 q = 0) : d354181 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d351949, d354181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d351949, d354181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d351950 q = 0) : d354182 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d351950, d354182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d351950, d354182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d351975 q = 0) : d354207 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d351975, d354207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351975, d354207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36603 q selected
  have h11 (q : Pattern) (selected : d351976 q = 0) : d354208 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d351976, d354208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d351976, d354208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d351977 q = 0) : d354209 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d351977, d354209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d351977, d354209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d351978 q = 0) : d354210 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d351978, d354210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d351978, d354210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d351979 q = 0) : d354211 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d351979, d354211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d351979, d354211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d351980 q = 0) : d354212 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d351980, d354212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d351980, d354212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro36605 (p : Pattern) (selected : d351990 p = 0) : d354222 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d351928 q = 0) : d354160 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d351928, d354160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36595 q selected
    | true =>
      simp only [d351928, d354160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d351986 q = 0) : d354218 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d351986, d354218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351986, d354218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d351987 q = 0) : d354219 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d351987, d354219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d351987, d354219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d351988 q = 0) : d354220 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d351988, d354220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351988, d354220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d351989 q = 0) : d354221 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d351989, d354221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351989, d354221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d351990 q = 0) : d354222 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d351990, d354222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351990, d354222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro36606 (p : Pattern) (selected : d351997 p = 0) : d354229 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d351928 q = 0) : d354160 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d351928, d354160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36595 q selected
    | true =>
      simp only [d351928, d354160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d351986 q = 0) : d354218 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d351986, d354218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351986, d354218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d351987 q = 0) : d354219 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d351987, d354219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d351987, d354219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d351988 q = 0) : d354220 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d351988, d354220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351988, d354220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d351989 q = 0) : d354221 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d351989, d354221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351989, d354221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d351935 q = 0) : d354167 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d351935, d354167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36597 q selected
    | true =>
      simp only [d351935, d354167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d351993 q = 0) : d354225 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d351993, d354225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351993, d354225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d351994 q = 0) : d354226 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d351994, d354226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d351994, d354226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d351995 q = 0) : d354227 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d351995, d354227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351995, d354227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d351996 q = 0) : d354228 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d351996, d354228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351996, d354228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d351997 q = 0) : d354229 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d351997, d354229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d351997, d354229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro36607 (p : Pattern) (selected : d352002 p = 0) : d354234 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d351922 q = 0) : d354154 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d351922, d354154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36594 q selected
    | true =>
      simp only [d351922, d354154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d351923 q = 0) : d354155 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d351923, d354155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351923, d354155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d351924 q = 0) : d354156 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d351924, d354156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d351924, d354156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d351925 q = 0) : d354157 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d351925, d354157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d351925, d354157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352001 q = 0) : d354233 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352001, d354233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352001, d354233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352002 q = 0) : d354234 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352002, d354234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352002, d354234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro36608 (p : Pattern) (selected : d352009 p = 0) : d354241 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d351922 q = 0) : d354154 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d351922, d354154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36594 q selected
    | true =>
      simp only [d351922, d354154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d351923 q = 0) : d354155 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d351923, d354155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351923, d354155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d351924 q = 0) : d354156 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d351924, d354156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d351924, d354156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352007 q = 0) : d354239 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352007, d354239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352007, d354239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352008 q = 0) : d354240 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352008, d354240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352008, d354240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352009 q = 0) : d354241 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352009, d354241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352009, d354241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro36609 (p : Pattern) (selected : d352015 p = 0) : d354247 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1 q = 0) : d0 q = 1 := by
    change (1 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d253268 q = 0) : d253269 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d253268, d253269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253268, d253269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d253269 q = 0) : d253268 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d253269, d253268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d253269, d253268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352013 q = 0) : d354245 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d352013, d354245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352013, d354245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d351901 q = 0) : d354133 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d351901, d354133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d351901, d354133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352014 q = 0) : d354246 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d352014, d354246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352014, d354246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d351902 q = 0) : d354134 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d351902, d354134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d351902, d354134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d352015 q = 0) : d354247 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d352015, d354247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352015, d354247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro36610 (p : Pattern) (selected : d352021 p = 0) : d354253 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352016 q = 0) : d354248 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d352016, d354248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36609 q selected
    | true =>
      simp only [d352016, d354248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352017 q = 0) : d354249 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d352017, d354249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d352017, d354249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d351904 q = 0) : d354136 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d351904, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36591 q selected
    | true =>
      simp only [d351904, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d351905 q = 0) : d354137 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d351905, d354137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d351905, d354137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352018 q = 0) : d354250 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d352018, d354250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352018, d354250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d351906 q = 0) : d354138 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d351906, d354138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d351906, d354138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352019 q = 0) : d354251 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d352019, d354251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352019, d354251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d352020 q = 0) : d354252 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d352020, d354252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352020, d354252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d351907 q = 0) : d354139 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d351907, d354139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d351907, d354139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d351908 q = 0) : d354140 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d351908, d354140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d351908, d354140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d352021 q = 0) : d354253 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d352021, d354253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d352021, d354253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro36611 (p : Pattern) (selected : d352027 p = 0) : d354259 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352022 q = 0) : d354254 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352022, d354254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36610 q selected
    | true =>
      simp only [d352022, d354254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352023 q = 0) : d354255 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352023, d354255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d352023, d354255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d352024 q = 0) : d354256 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352024, d354256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352024, d354256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d352025 q = 0) : d354257 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d352025, d354257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352025, d354257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d351910 q = 0) : d354142 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d351910, d354142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36592 q selected
    | true =>
      simp only [d351910, d354142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d351911 q = 0) : d354143 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d351911, d354143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d351911, d354143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d351912 q = 0) : d354144 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d351912, d354144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351912, d354144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d351913 q = 0) : d354145 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d351913, d354145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d351913, d354145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d352026 q = 0) : d354258 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d352026, d354258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352026, d354258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d351914 q = 0) : d354146 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d351914, d354146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d351914, d354146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d352027 q = 0) : d354259 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d352027, d354259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d352027, d354259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro36612 (p : Pattern) (selected : d352033 p = 0) : d354265 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352028 q = 0) : d354260 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d352028, d354260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36611 q selected
    | true =>
      simp only [d352028, d354260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36593 q selected
  have h2 (q : Pattern) (selected : d352029 q = 0) : d354261 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d352029, d354261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352029, d354261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352030 q = 0) : d354262 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d352030, d354262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352030, d354262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d351916 q = 0) : d354148 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d351916, d354148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36593 q selected
    | true =>
      simp only [d351916, d354148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d351917 q = 0) : d354149 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d351917, d354149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351917, d354149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d351918 q = 0) : d354150 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d351918, d354150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351918, d354150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d352031 q = 0) : d354263 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d352031, d354263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352031, d354263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d351919 q = 0) : d354151 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d351919, d354151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d351919, d354151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d352032 q = 0) : d354264 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d352032, d354264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352032, d354264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d352033 q = 0) : d354265 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d352033, d354265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d352033, d354265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro36613 (p : Pattern) (selected : d352039 p = 0) : d354271 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352034 q = 0) : d354266 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352034, d354266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36612 q selected
    | true =>
      simp only [d352034, d354266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352035 q = 0) : d354267 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352035, d354267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352035, d354267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d351922 q = 0) : d354154 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d351922, d354154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36594 q selected
    | true =>
      simp only [d351922, d354154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d351923 q = 0) : d354155 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d351923, d354155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351923, d354155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352036 q = 0) : d354268 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d352036, d354268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352036, d354268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352037 q = 0) : d354269 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352037, d354269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352037, d354269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352038 q = 0) : d354270 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352038, d354270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352038, d354270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d352039 q = 0) : d354271 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352039, d354271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352039, d354271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro36614 (p : Pattern) (selected : d352044 p = 0) : d354135 p = 1 := by
  have h0 (q : Pattern) (selected : d2 q = 0) : d0 q = 1 := by
    change (2 : Int) = 0 at selected
    omega
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d352041 q = 0) : d253268 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d352041, d253268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352041, d253268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352042 q = 0) : d354133 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d352042, d354133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352042, d354133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d352043 q = 0) : d354134 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d352043, d354134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352043, d354134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d352044 q = 0) : d354135 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d352044, d354135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352044, d354135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h5 p selected
theorem eqIntro36615 (p : Pattern) (selected : d352050 p = 0) : d354141 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352045 q = 0) : d354136 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d352045, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36614 q selected
    | true =>
      simp only [d352045, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352046 q = 0) : d354137 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d352046, d354137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d352046, d354137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d352047 q = 0) : d354138 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d352047, d354138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352047, d354138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352048 q = 0) : d354139 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d352048, d354139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352048, d354139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352049 q = 0) : d354140 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d352049, d354140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352049, d354140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352050 q = 0) : d354141 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d352050, d354141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352050, d354141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36616 (p : Pattern) (selected : d352056 p = 0) : d354147 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352051 q = 0) : d354142 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352051, d354142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36615 q selected
    | true =>
      simp only [d352051, d354142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352052 q = 0) : d354143 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352052, d354143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d352052, d354143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d352053 q = 0) : d354144 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352053, d354144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352053, d354144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d352054 q = 0) : d354145 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d352054, d354145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352054, d354145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352055 q = 0) : d354146 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d352055, d354146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352055, d354146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352056 q = 0) : d354147 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d352056, d354147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352056, d354147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36617 (p : Pattern) (selected : d352062 p = 0) : d354153 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352057 q = 0) : d354148 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d352057, d354148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36616 q selected
    | true =>
      simp only [d352057, d354148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352058 q = 0) : d354149 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d352058, d354149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352058, d354149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352059 q = 0) : d354150 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d352059, d354150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352059, d354150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d352060 q = 0) : d354151 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d352060, d354151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352060, d354151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352061 q = 0) : d354152 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d352061, d354152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352061, d354152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352062 q = 0) : d354153 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d352062, d354153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352062, d354153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36618 (p : Pattern) (selected : d352068 p = 0) : d354159 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352063 q = 0) : d354154 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352063, d354154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36617 q selected
    | true =>
      simp only [d352063, d354154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352064 q = 0) : d354155 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352064, d354155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352064, d354155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352065 q = 0) : d354156 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d352065, d354156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352065, d354156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352066 q = 0) : d354157 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352066, d354157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352066, d354157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352067 q = 0) : d354158 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352067, d354158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352067, d354158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352068 q = 0) : d354159 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352068, d354159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352068, d354159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro36619 (p : Pattern) (selected : d352074 p = 0) : d354277 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352003 q = 0) : d354235 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352003, d354235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36607 q selected
    | true =>
      simp only [d352003, d354235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352004 q = 0) : d354236 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352004, d354236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352004, d354236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352005 q = 0) : d354237 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352005, d354237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352005, d354237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352006 q = 0) : d354238 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d352006, d354238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352006, d354238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352010 q = 0) : d354242 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352010, d354242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36608 q selected
    | true =>
      simp only [d352010, d354242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352011 q = 0) : d354243 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352011, d354243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352011, d354243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d352012 q = 0) : d354244 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352012, d354244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352012, d354244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d352040 q = 0) : d354272 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352040, d354272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36613 q selected
    | true =>
      simp only [d352040, d354272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36595 q selected
  have h9 (q : Pattern) (selected : d352069 q = 0) : d354160 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352069, d354160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36618 q selected
    | true =>
      simp only [d352069, d354160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d352070 q = 0) : d354273 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352070, d354273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d352070, d354273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d351928 q = 0) : d354160 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d351928, d354160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36595 q selected
    | true =>
      simp only [d351928, d354160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d351929 q = 0) : d354161 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d351929, d354161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d351929, d354161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d352071 q = 0) : d354274 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352071, d354274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d352071, d354274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d352072 q = 0) : d354275 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d352072, d354275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352072, d354275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d352073 q = 0) : d354276 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d352073, d354276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352073, d354276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d352074 q = 0) : d354277 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d352074, d354277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352074, d354277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro36620 (p : Pattern) (selected : d352075 p = 0) : d354278 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d351922 q = 0) : d354154 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d351922, d354154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36594 q selected
    | true =>
      simp only [d351922, d354154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d351923 q = 0) : d354155 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d351923, d354155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351923, d354155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d351924 q = 0) : d354156 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d351924, d354156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d351924, d354156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d351925 q = 0) : d354157 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d351925, d354157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d351925, d354157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352001 q = 0) : d354233 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352001, d354233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352001, d354233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352075 q = 0) : d354278 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352075, d354278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352075, d354278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36621 (p : Pattern) (selected : d352080 p = 0) : d354283 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d351922 q = 0) : d354154 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d351922, d354154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36594 q selected
    | true =>
      simp only [d351922, d354154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d351923 q = 0) : d354155 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d351923, d354155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351923, d354155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d351924 q = 0) : d354156 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d351924, d354156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d351924, d354156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352007 q = 0) : d354239 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352007, d354239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352007, d354239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352008 q = 0) : d354240 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352008, d354240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352008, d354240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352080 q = 0) : d354283 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352080, d354283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352080, d354283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36622 (p : Pattern) (selected : d352084 p = 0) : d354287 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352034 q = 0) : d354266 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352034, d354266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36612 q selected
    | true =>
      simp only [d352034, d354266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352035 q = 0) : d354267 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352035, d354267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352035, d354267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d351922 q = 0) : d354154 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d351922, d354154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36594 q selected
    | true =>
      simp only [d351922, d354154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d351923 q = 0) : d354155 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d351923, d354155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351923, d354155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352036 q = 0) : d354268 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d352036, d354268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352036, d354268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352037 q = 0) : d354269 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352037, d354269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352037, d354269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352038 q = 0) : d354270 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352038, d354270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352038, d354270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d352084 q = 0) : d354287 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352084, d354287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352084, d354287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro36623 (p : Pattern) (selected : d352086 p = 0) : d354166 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352063 q = 0) : d354154 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352063, d354154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36617 q selected
    | true =>
      simp only [d352063, d354154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352064 q = 0) : d354155 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352064, d354155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352064, d354155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352065 q = 0) : d354156 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d352065, d354156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352065, d354156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352066 q = 0) : d354157 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352066, d354157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352066, d354157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352067 q = 0) : d354158 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352067, d354158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352067, d354158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352086 q = 0) : d354166 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352086, d354166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352086, d354166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36624 (p : Pattern) (selected : d352092 p = 0) : d354293 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352003 q = 0) : d354235 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352003, d354235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36607 q selected
    | true =>
      simp only [d352003, d354235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352004 q = 0) : d354236 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352004, d354236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352004, d354236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352005 q = 0) : d354237 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352005, d354237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352005, d354237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352006 q = 0) : d354238 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d352006, d354238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352006, d354238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352010 q = 0) : d354242 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352010, d354242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36608 q selected
    | true =>
      simp only [d352010, d354242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352011 q = 0) : d354243 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352011, d354243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352011, d354243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d352012 q = 0) : d354244 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352012, d354244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352012, d354244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d352040 q = 0) : d354272 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352040, d354272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36613 q selected
    | true =>
      simp only [d352040, d354272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36595 q selected
  have h9 (q : Pattern) (selected : d352069 q = 0) : d354160 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352069, d354160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36618 q selected
    | true =>
      simp only [d352069, d354160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d352070 q = 0) : d354273 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352070, d354273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d352070, d354273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d351928 q = 0) : d354160 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d351928, d354160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36595 q selected
    | true =>
      simp only [d351928, d354160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d351929 q = 0) : d354161 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d351929, d354161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d351929, d354161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d352071 q = 0) : d354274 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352071, d354274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d352071, d354274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d352072 q = 0) : d354275 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d352072, d354275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352072, d354275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d352073 q = 0) : d354276 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d352073, d354276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352073, d354276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d352076 q = 0) : d354279 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352076, d354279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36620 q selected
    | true =>
      simp only [d352076, d354279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d352077 q = 0) : d354280 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352077, d354280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352077, d354280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d352078 q = 0) : d354281 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352078, d354281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d352078, d354281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d352079 q = 0) : d354282 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d352079, d354282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352079, d354282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d352081 q = 0) : d354284 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352081, d354284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36621 q selected
    | true =>
      simp only [d352081, d354284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d352082 q = 0) : d354285 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352082, d354285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352082, d354285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d352083 q = 0) : d354286 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352083, d354286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d352083, d354286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d352085 q = 0) : d354288 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352085, d354288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36622 q selected
    | true =>
      simp only [d352085, d354288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36597 q selected
  have h24 (q : Pattern) (selected : d352087 q = 0) : d354167 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352087, d354167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36623 q selected
    | true =>
      simp only [d352087, d354167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d352088 q = 0) : d354289 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352088, d354289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d352088, d354289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d351935 q = 0) : d354167 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d351935, d354167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36597 q selected
    | true =>
      simp only [d351935, d354167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d351936 q = 0) : d354168 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d351936, d354168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d351936, d354168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d352089 q = 0) : d354290 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352089, d354290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d352089, d354290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d352090 q = 0) : d354291 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d352090, d354291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d352090, d354291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d352091 q = 0) : d354292 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d352091, d354292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d352091, d354292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d352092 q = 0) : d354293 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d352092, d354293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d352092, d354293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro36625 (p : Pattern) (selected : d352094 p = 0) : d354295 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d351928 q = 0) : d354160 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d351928, d354160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36595 q selected
    | true =>
      simp only [d351928, d354160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d351986 q = 0) : d354218 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d351986, d354218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351986, d354218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d351987 q = 0) : d354219 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d351987, d354219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d351987, d354219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d351988 q = 0) : d354220 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d351988, d354220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351988, d354220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d351989 q = 0) : d354221 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d351989, d354221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351989, d354221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352094 q = 0) : d354295 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d352094, d354295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352094, d354295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36626 (p : Pattern) (selected : d352101 p = 0) : d354302 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352085 q = 0) : d354288 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352085, d354288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36622 q selected
    | true =>
      simp only [d352085, d354288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36597 q selected
  have h2 (q : Pattern) (selected : d352087 q = 0) : d354167 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352087, d354167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36623 q selected
    | true =>
      simp only [d352087, d354167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d352088 q = 0) : d354289 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352088, d354289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d352088, d354289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d351935 q = 0) : d354167 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d351935, d354167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36597 q selected
    | true =>
      simp only [d351935, d354167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d351936 q = 0) : d354168 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d351936, d354168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d351936, d354168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352089 q = 0) : d354290 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352089, d354290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352089, d354290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d352099 q = 0) : d354300 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d352099, d354300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352099, d354300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d352100 q = 0) : d354301 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d352100, d354301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352100, d354301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d352101 q = 0) : d354302 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d352101, d354302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352101, d354302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro36627 (p : Pattern) (selected : d352112 p = 0) : d354313 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352107 q = 0) : d354308 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352107, d354308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352107, d354308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36610 q selected
  have h2 (q : Pattern) (selected : d352022 q = 0) : d354254 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352022, d354254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36610 q selected
    | true =>
      simp only [d352022, d354254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d352108 q = 0) : d354309 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352108, d354309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d352108, d354309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d352023 q = 0) : d354255 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352023, d354255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352023, d354255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352109 q = 0) : d354310 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352109, d354310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352109, d354310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352110 q = 0) : d354311 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d352110, d354311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352110, d354311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d351951 q = 0) : d354183 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d351951, d354183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351951, d354183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36592 q selected
  have h8 (q : Pattern) (selected : d351910 q = 0) : d354142 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d351910, d354142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36592 q selected
    | true =>
      simp only [d351910, d354142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d351952 q = 0) : d354184 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d351952, d354184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d351952, d354184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d351911 q = 0) : d354143 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d351911, d354143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d351911, d354143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d351953 q = 0) : d354185 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d351953, d354185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d351953, d354185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d351954 q = 0) : d354186 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d351954, d354186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d351954, d354186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d352111 q = 0) : d354312 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d352111, d354312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352111, d354312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d351955 q = 0) : d354187 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d351955, d354187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d351955, d354187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d352112 q = 0) : d354313 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d352112, d354313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d352112, d354313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro36628 (p : Pattern) (selected : d352118 p = 0) : d354319 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352113 q = 0) : d354314 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d352113, d354314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36627 q selected
    | true =>
      simp only [d352113, d354314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36600 q selected
  have h2 (q : Pattern) (selected : d352114 q = 0) : d354315 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d352114, d354315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352114, d354315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352115 q = 0) : d354316 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d352115, d354316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352115, d354316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d351957 q = 0) : d354189 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d351957, d354189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36600 q selected
    | true =>
      simp only [d351957, d354189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d351958 q = 0) : d354190 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d351958, d354190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351958, d354190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d351959 q = 0) : d354191 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d351959, d354191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351959, d354191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d352116 q = 0) : d354317 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d352116, d354317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352116, d354317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d351960 q = 0) : d354192 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d351960, d354192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d351960, d354192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d352117 q = 0) : d354318 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d352117, d354318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352117, d354318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d352118 q = 0) : d354319 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d352118, d354319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d352118, d354319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro36629 (p : Pattern) (selected : d352124 p = 0) : d354325 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352119 q = 0) : d354320 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352119, d354320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36628 q selected
    | true =>
      simp only [d352119, d354320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352120 q = 0) : d354321 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352120, d354321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352120, d354321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d351963 q = 0) : d354195 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d351963, d354195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36601 q selected
    | true =>
      simp only [d351963, d354195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d351964 q = 0) : d354196 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d351964, d354196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351964, d354196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352121 q = 0) : d354322 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d352121, d354322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352121, d354322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352122 q = 0) : d354323 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352122, d354323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352122, d354323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352123 q = 0) : d354324 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352123, d354324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352123, d354324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d352124 q = 0) : d354325 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352124, d354325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352124, d354325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro36630 (p : Pattern) (selected : d352131 p = 0) : d354188 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352126 q = 0) : d354183 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352126, d354183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352126, d354183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36615 q selected
  have h2 (q : Pattern) (selected : d352051 q = 0) : d354142 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352051, d354142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36615 q selected
    | true =>
      simp only [d352051, d354142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d352127 q = 0) : d354184 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352127, d354184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d352127, d354184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d352052 q = 0) : d354143 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352052, d354143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352052, d354143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352128 q = 0) : d354185 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352128, d354185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352128, d354185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352129 q = 0) : d354186 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d352129, d354186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352129, d354186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352130 q = 0) : d354187 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d352130, d354187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352130, d354187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d352131 q = 0) : d354188 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d352131, d354188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352131, d354188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro36631 (p : Pattern) (selected : d352137 p = 0) : d354194 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352132 q = 0) : d354189 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d352132, d354189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36630 q selected
    | true =>
      simp only [d352132, d354189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352133 q = 0) : d354190 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d352133, d354190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352133, d354190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352134 q = 0) : d354191 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d352134, d354191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352134, d354191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d352135 q = 0) : d354192 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d352135, d354192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352135, d354192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352136 q = 0) : d354193 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d352136, d354193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352136, d354193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352137 q = 0) : d354194 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d352137, d354194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352137, d354194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36632 (p : Pattern) (selected : d352143 p = 0) : d354200 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352138 q = 0) : d354195 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352138, d354195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36631 q selected
    | true =>
      simp only [d352138, d354195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352139 q = 0) : d354196 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352139, d354196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352139, d354196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352140 q = 0) : d354197 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d352140, d354197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352140, d354197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352141 q = 0) : d354198 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352141, d354198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352141, d354198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352142 q = 0) : d354199 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352142, d354199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352142, d354199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352143 q = 0) : d354200 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352143, d354200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352143, d354200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36633 (p : Pattern) (selected : d352149 p = 0) : d354331 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352125 q = 0) : d354326 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352125, d354326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36629 q selected
    | true =>
      simp only [d352125, d354326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36602 q selected
  have h2 (q : Pattern) (selected : d352144 q = 0) : d354201 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352144, d354201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36632 q selected
    | true =>
      simp only [d352144, d354201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d352145 q = 0) : d354327 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352145, d354327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d352145, d354327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d351969 q = 0) : d354201 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d351969, d354201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36602 q selected
    | true =>
      simp only [d351969, d354201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d351970 q = 0) : d354202 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d351970, d354202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d351970, d354202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352146 q = 0) : d354328 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352146, d354328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352146, d354328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d352147 q = 0) : d354329 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d352147, d354329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352147, d354329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d352148 q = 0) : d354330 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d352148, d354330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352148, d354330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d352149 q = 0) : d354331 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d352149, d354331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352149, d354331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro36634 (p : Pattern) (selected : d352155 p = 0) : d354337 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d351991 q = 0) : d354223 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d351991, d354223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351991, d354223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36605 q selected
  have h2 (q : Pattern) (selected : d351992 q = 0) : d354224 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d351992, d354224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d351992, d354224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d351998 q = 0) : d354230 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d351998, d354230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36605 q selected
    | true =>
      simp only [d351998, d354230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36606 q selected
  have h4 (q : Pattern) (selected : d351999 q = 0) : d354231 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d351999, d354231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d351999, d354231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352000 q = 0) : d354232 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d352000, d354232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352000, d354232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352093 q = 0) : d354294 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d352093, d354294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36619 q selected
    | true =>
      simp only [d352093, d354294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36624 q selected
  have h7 (q : Pattern) (selected : d352095 q = 0) : d354296 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d352095, d354296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36625 q selected
    | true =>
      simp only [d352095, d354296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d352096 q = 0) : d354297 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d352096, d354297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352096, d354297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d352097 q = 0) : d354298 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d352097, d354298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d352097, d354298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d352098 q = 0) : d354299 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d352098, d354299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352098, d354299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d352102 q = 0) : d354303 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d352102, d354303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352102, d354303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36626 q selected
  have h12 (q : Pattern) (selected : d352103 q = 0) : d354304 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d352103, d354304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d352103, d354304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d352104 q = 0) : d354305 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d352104, d354305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d352104, d354305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d352105 q = 0) : d354306 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d352105, d354306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d352105, d354306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d352106 q = 0) : d354307 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d352106, d354307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d352106, d354307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d352150 q = 0) : d354332 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d352150, d354332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352150, d354332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36633 q selected
  have h17 (q : Pattern) (selected : d352151 q = 0) : d354333 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d352151, d354333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d352151, d354333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d352152 q = 0) : d354334 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d352152, d354334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d352152, d354334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d352153 q = 0) : d354335 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d352153, d354335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d352153, d354335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d352154 q = 0) : d354336 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d352154, d354336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d352154, d354336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d352155 q = 0) : d354337 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d352155, d354337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d352155, d354337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro36635 (p : Pattern) (selected : d352161 p = 0) : d354343 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d351981 q = 0) : d354213 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d351981, d354213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351981, d354213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36604 q selected
  have h2 (q : Pattern) (selected : d351982 q = 0) : d354214 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d351982, d354214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351982, d354214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d351983 q = 0) : d354215 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d351983, d354215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351983, d354215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d351984 q = 0) : d354216 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d351984, d354216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351984, d354216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d351985 q = 0) : d354217 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d351985, d354217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351985, d354217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352156 q = 0) : d354338 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d352156, d354338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352156, d354338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36634 q selected
  have h7 (q : Pattern) (selected : d352157 q = 0) : d354339 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d352157, d354339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352157, d354339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d352158 q = 0) : d354340 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d352158, d354340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352158, d354340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d352159 q = 0) : d354341 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d352159, d354341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352159, d354341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d352160 q = 0) : d354342 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d352160, d354342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352160, d354342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d352161 q = 0) : d354343 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d352161, d354343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352161, d354343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro36636 (p : Pattern) (selected : d352166 p = 0) : d354348 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352040 q = 0) : d354272 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352040, d354272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36613 q selected
    | true =>
      simp only [d352040, d354272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36595 q selected
  have h2 (q : Pattern) (selected : d352162 q = 0) : d354344 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352162, d354344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352162, d354344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352163 q = 0) : d354345 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352163, d354345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352163, d354345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352164 q = 0) : d354346 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d352164, d354346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352164, d354346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352165 q = 0) : d354347 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d352165, d354347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352165, d354347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352166 q = 0) : d354348 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d352166, d354348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352166, d354348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro36637 (p : Pattern) (selected : d352173 p = 0) : d354355 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352040 q = 0) : d354272 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352040, d354272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36613 q selected
    | true =>
      simp only [d352040, d354272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36595 q selected
  have h2 (q : Pattern) (selected : d352162 q = 0) : d354344 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352162, d354344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352162, d354344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352163 q = 0) : d354345 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352163, d354345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352163, d354345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352164 q = 0) : d354346 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d352164, d354346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352164, d354346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352165 q = 0) : d354347 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d352165, d354347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352165, d354347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352085 q = 0) : d354288 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352085, d354288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36622 q selected
    | true =>
      simp only [d352085, d354288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36597 q selected
  have h7 (q : Pattern) (selected : d352169 q = 0) : d354351 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352169, d354351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352169, d354351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d352170 q = 0) : d354352 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352170, d354352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352170, d354352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d352171 q = 0) : d354353 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d352171, d354353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352171, d354353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d352172 q = 0) : d354354 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d352172, d354354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352172, d354354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d352173 q = 0) : d354355 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d352173, d354355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352173, d354355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro36638 (p : Pattern) (selected : d352178 p = 0) : d354360 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352034 q = 0) : d354266 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352034, d354266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36612 q selected
    | true =>
      simp only [d352034, d354266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352035 q = 0) : d354267 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352035, d354267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352035, d354267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d351922 q = 0) : d354154 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d351922, d354154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36594 q selected
    | true =>
      simp only [d351922, d354154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d351923 q = 0) : d354155 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d351923, d354155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351923, d354155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352036 q = 0) : d354268 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d352036, d354268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352036, d354268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352037 q = 0) : d354269 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352037, d354269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352037, d354269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352177 q = 0) : d354359 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352177, d354359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352177, d354359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d352178 q = 0) : d354360 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352178, d354360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352178, d354360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro36639 (p : Pattern) (selected : d352185 p = 0) : d354367 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352034 q = 0) : d354266 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352034, d354266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36612 q selected
    | true =>
      simp only [d352034, d354266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352035 q = 0) : d354267 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352035, d354267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352035, d354267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d351922 q = 0) : d354154 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d351922, d354154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36594 q selected
    | true =>
      simp only [d351922, d354154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d351923 q = 0) : d354155 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d351923, d354155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351923, d354155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352036 q = 0) : d354268 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d352036, d354268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352036, d354268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352183 q = 0) : d354365 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352183, d354365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352183, d354365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d352184 q = 0) : d354366 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352184, d354366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352184, d354366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d352185 q = 0) : d354367 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352185, d354367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352185, d354367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro36640 (p : Pattern) (selected : d352192 p = 0) : d354374 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1 q = 0) : d0 q = 1 := by
    change (1 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d253268 q = 0) : d253269 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d253268, d253269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253268, d253269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352189 q = 0) : d354371 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d352189, d354371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352189, d354371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d253269 q = 0) : d253268 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d253269, d253268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d253269, d253268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352190 q = 0) : d354372 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d352190, d354372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352190, d354372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352191 q = 0) : d354373 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d352191, d354373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352191, d354373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d352013 q = 0) : d354245 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d352013, d354245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352013, d354245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h8 (q : Pattern) (selected : d351901 q = 0) : d354133 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d351901, d354133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d351901, d354133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d352014 q = 0) : d354246 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d352014, d354246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352014, d354246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d352192 q = 0) : d354374 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d352192, d354374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352192, d354374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro36641 (p : Pattern) (selected : d352198 p = 0) : d354380 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352193 q = 0) : d354375 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d352193, d354375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36640 q selected
    | true =>
      simp only [d352193, d354375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352194 q = 0) : d354376 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d352194, d354376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d352194, d354376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d352016 q = 0) : d354248 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d352016, d354248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36609 q selected
    | true =>
      simp only [d352016, d354248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352017 q = 0) : d354249 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d352017, d354249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352017, d354249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352195 q = 0) : d354377 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d352195, d354377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352195, d354377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d351904 q = 0) : d354136 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d351904, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36591 q selected
    | true =>
      simp only [d351904, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d351905 q = 0) : d354137 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d351905, d354137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d351905, d354137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d352018 q = 0) : d354250 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d352018, d354250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352018, d354250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d352196 q = 0) : d354378 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d352196, d354378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352196, d354378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d352197 q = 0) : d354379 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d352197, d354379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d352197, d354379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d351906 q = 0) : d354138 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d351906, d354138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d351906, d354138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d352019 q = 0) : d354251 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d352019, d354251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d352019, d354251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d352020 q = 0) : d354252 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d352020, d354252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d352020, d354252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d352198 q = 0) : d354380 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d352198, d354380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d352198, d354380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro36642 (p : Pattern) (selected : d352206 p = 0) : d354388 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352016 q = 0) : d354248 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d352016, d354248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36609 q selected
    | true =>
      simp only [d352016, d354248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352017 q = 0) : d354249 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d352017, d354249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d352017, d354249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d351904 q = 0) : d354136 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d351904, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36591 q selected
    | true =>
      simp only [d351904, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d351905 q = 0) : d354137 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d351905, d354137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d351905, d354137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352018 q = 0) : d354250 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d352018, d354250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352018, d354250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352204 q = 0) : d354386 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d352204, d354386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352204, d354386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352205 q = 0) : d354387 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d352205, d354387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352205, d354387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d351906 q = 0) : d354138 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d351906, d354138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d351906, d354138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d351907 q = 0) : d354139 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d351907, d354139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d351907, d354139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d351908 q = 0) : d354140 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d351908, d354140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d351908, d354140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d352206 q = 0) : d354388 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d352206, d354388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352206, d354388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro36643 (p : Pattern) (selected : d352212 p = 0) : d354394 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352199 q = 0) : d354381 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352199, d354381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36641 q selected
    | true =>
      simp only [d352199, d354381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352200 q = 0) : d354382 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352200, d354382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d352200, d354382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d352201 q = 0) : d354383 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352201, d354383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352201, d354383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d352202 q = 0) : d354384 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d352202, d354384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352202, d354384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352022 q = 0) : d354254 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352022, d354254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36610 q selected
    | true =>
      simp only [d352022, d354254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352023 q = 0) : d354255 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352023, d354255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352023, d354255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352024 q = 0) : d354256 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352024, d354256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352024, d354256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d352025 q = 0) : d354257 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d352025, d354257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352025, d354257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d352203 q = 0) : d354385 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d352203, d354385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352203, d354385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d352207 q = 0) : d354389 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352207, d354389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36642 q selected
    | true =>
      simp only [d352207, d354389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d352208 q = 0) : d354390 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352208, d354390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d352208, d354390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d352209 q = 0) : d354391 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352209, d354391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352209, d354391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d352210 q = 0) : d354392 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d352210, d354392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d352210, d354392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d351910 q = 0) : d354142 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d351910, d354142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36592 q selected
    | true =>
      simp only [d351910, d354142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d351911 q = 0) : d354143 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d351911, d354143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d351911, d354143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d351912 q = 0) : d354144 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d351912, d354144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351912, d354144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d351913 q = 0) : d354145 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d351913, d354145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d351913, d354145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d352211 q = 0) : d354393 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d352211, d354393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d352211, d354393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d352212 q = 0) : d354394 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d352212, d354394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d352212, d354394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro36644 (p : Pattern) (selected : d352218 p = 0) : d354400 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352213 q = 0) : d354395 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d352213, d354395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36643 q selected
    | true =>
      simp only [d352213, d354395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36611 q selected
  have h2 (q : Pattern) (selected : d352214 q = 0) : d354396 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d352214, d354396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352214, d354396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352215 q = 0) : d354397 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d352215, d354397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352215, d354397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d352028 q = 0) : d354260 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d352028, d354260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36611 q selected
    | true =>
      simp only [d352028, d354260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36593 q selected
  have h5 (q : Pattern) (selected : d352029 q = 0) : d354261 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d352029, d354261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352029, d354261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352030 q = 0) : d354262 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d352030, d354262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352030, d354262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d352216 q = 0) : d354398 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d352216, d354398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352216, d354398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d351916 q = 0) : d354148 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d351916, d354148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36593 q selected
    | true =>
      simp only [d351916, d354148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d351917 q = 0) : d354149 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d351917, d354149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351917, d354149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d351918 q = 0) : d354150 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d351918, d354150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351918, d354150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d352031 q = 0) : d354263 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d352031, d354263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352031, d354263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d352217 q = 0) : d354399 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d352217, d354399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352217, d354399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d352218 q = 0) : d354400 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d352218, d354400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d352218, d354400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro36645 (p : Pattern) (selected : d352224 p = 0) : d354406 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352219 q = 0) : d354401 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352219, d354401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36644 q selected
    | true =>
      simp only [d352219, d354401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352220 q = 0) : d354402 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352220, d354402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352220, d354402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352034 q = 0) : d354266 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352034, d354266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36612 q selected
    | true =>
      simp only [d352034, d354266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352035 q = 0) : d354267 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352035, d354267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352035, d354267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352221 q = 0) : d354403 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d352221, d354403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352221, d354403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352222 q = 0) : d354404 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352222, d354404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352222, d354404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352223 q = 0) : d354405 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352223, d354405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352223, d354405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d352224 q = 0) : d354406 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352224, d354406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352224, d354406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro36646 (p : Pattern) (selected : d352228 p = 0) : d354247 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2 q = 0) : d0 q = 1 := by
    change (2 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d351450 q = 0) : d253269 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d351450, d253269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351450, d253269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352041 q = 0) : d253268 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d352041, d253268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d352041, d253268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352226 q = 0) : d354245 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d352226, d354245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352226, d354245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352042 q = 0) : d354133 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d352042, d354133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352042, d354133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352227 q = 0) : d354246 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d352227, d354246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352227, d354246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d352043 q = 0) : d354134 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d352043, d354134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352043, d354134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d352228 q = 0) : d354247 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d352228, d354247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352228, d354247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro36647 (p : Pattern) (selected : d352234 p = 0) : d354253 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352229 q = 0) : d354248 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d352229, d354248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36646 q selected
    | true =>
      simp only [d352229, d354248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352230 q = 0) : d354249 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d352230, d354249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d352230, d354249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d352045 q = 0) : d354136 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d352045, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36614 q selected
    | true =>
      simp only [d352045, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352046 q = 0) : d354137 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d352046, d354137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352046, d354137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352231 q = 0) : d354250 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d352231, d354250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352231, d354250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352047 q = 0) : d354138 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d352047, d354138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352047, d354138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352232 q = 0) : d354251 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d352232, d354251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352232, d354251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d352233 q = 0) : d354252 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d352233, d354252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352233, d354252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d352048 q = 0) : d354139 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d352048, d354139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352048, d354139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d352049 q = 0) : d354140 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d352049, d354140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d352049, d354140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d352234 q = 0) : d354253 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d352234, d354253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d352234, d354253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro36648 (p : Pattern) (selected : d352240 p = 0) : d354259 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352235 q = 0) : d354254 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352235, d354254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36647 q selected
    | true =>
      simp only [d352235, d354254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352236 q = 0) : d354255 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352236, d354255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d352236, d354255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d352237 q = 0) : d354256 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352237, d354256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352237, d354256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d352238 q = 0) : d354257 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d352238, d354257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352238, d354257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352051 q = 0) : d354142 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352051, d354142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36615 q selected
    | true =>
      simp only [d352051, d354142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352052 q = 0) : d354143 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352052, d354143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352052, d354143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352053 q = 0) : d354144 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352053, d354144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352053, d354144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d352054 q = 0) : d354145 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d352054, d354145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352054, d354145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d352239 q = 0) : d354258 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d352239, d354258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352239, d354258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d352055 q = 0) : d354146 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d352055, d354146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d352055, d354146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d352240 q = 0) : d354259 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d352240, d354259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d352240, d354259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro36649 (p : Pattern) (selected : d352246 p = 0) : d354265 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352241 q = 0) : d354260 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d352241, d354260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36648 q selected
    | true =>
      simp only [d352241, d354260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36616 q selected
  have h2 (q : Pattern) (selected : d352242 q = 0) : d354261 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d352242, d354261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352242, d354261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352243 q = 0) : d354262 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d352243, d354262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352243, d354262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d352057 q = 0) : d354148 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d352057, d354148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36616 q selected
    | true =>
      simp only [d352057, d354148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352058 q = 0) : d354149 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d352058, d354149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352058, d354149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352059 q = 0) : d354150 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d352059, d354150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352059, d354150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d352244 q = 0) : d354263 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d352244, d354263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352244, d354263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d352060 q = 0) : d354151 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d352060, d354151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352060, d354151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d352245 q = 0) : d354264 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d352245, d354264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352245, d354264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d352246 q = 0) : d354265 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d352246, d354265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d352246, d354265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro36650 (p : Pattern) (selected : d352252 p = 0) : d354271 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352247 q = 0) : d354266 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352247, d354266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36649 q selected
    | true =>
      simp only [d352247, d354266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352248 q = 0) : d354267 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352248, d354267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352248, d354267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352063 q = 0) : d354154 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352063, d354154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36617 q selected
    | true =>
      simp only [d352063, d354154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352064 q = 0) : d354155 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352064, d354155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352064, d354155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352249 q = 0) : d354268 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d352249, d354268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352249, d354268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352250 q = 0) : d354269 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352250, d354269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352250, d354269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352251 q = 0) : d354270 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352251, d354270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352251, d354270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d352252 q = 0) : d354271 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352252, d354271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352252, d354271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro36651 (p : Pattern) (selected : d352258 p = 0) : d354412 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352034 q = 0) : d354266 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352034, d354266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36612 q selected
    | true =>
      simp only [d352034, d354266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352035 q = 0) : d354267 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352035, d354267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352035, d354267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352255 q = 0) : d354409 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d352255, d354409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352255, d354409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352256 q = 0) : d354410 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352256, d354410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352256, d354410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352257 q = 0) : d354411 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352257, d354411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352257, d354411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352258 q = 0) : d354412 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352258, d354412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352258, d354412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro36652 (p : Pattern) (selected : d352264 p = 0) : d354418 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352179 q = 0) : d354361 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352179, d354361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36638 q selected
    | true =>
      simp only [d352179, d354361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36607 q selected
  have h2 (q : Pattern) (selected : d352180 q = 0) : d354362 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352180, d354362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352180, d354362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352181 q = 0) : d354363 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352181, d354363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352181, d354363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352182 q = 0) : d354364 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d352182, d354364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352182, d354364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352186 q = 0) : d354368 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352186, d354368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36639 q selected
    | true =>
      simp only [d352186, d354368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36608 q selected
  have h6 (q : Pattern) (selected : d352187 q = 0) : d354369 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352187, d354369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352187, d354369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d352188 q = 0) : d354370 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352188, d354370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352188, d354370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d352225 q = 0) : d354407 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352225, d354407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36645 q selected
    | true =>
      simp only [d352225, d354407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36613 q selected
  have h9 (q : Pattern) (selected : d352253 q = 0) : d354272 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352253, d354272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36650 q selected
    | true =>
      simp only [d352253, d354272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36618 q selected
  have h10 (q : Pattern) (selected : d352254 q = 0) : d354408 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352254, d354408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d352254, d354408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d352259 q = 0) : d354413 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352259, d354413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36651 q selected
    | true =>
      simp only [d352259, d354413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d352260 q = 0) : d354414 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352260, d354414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d352260, d354414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d352261 q = 0) : d354415 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352261, d354415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d352261, d354415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d352262 q = 0) : d354416 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d352262, d354416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352262, d354416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d352263 q = 0) : d354417 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d352263, d354417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352263, d354417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d352264 q = 0) : d354418 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d352264, d354418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352264, d354418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro36653 (p : Pattern) (selected : d352265 p = 0) : d354419 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352034 q = 0) : d354266 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352034, d354266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36612 q selected
    | true =>
      simp only [d352034, d354266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352035 q = 0) : d354267 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352035, d354267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352035, d354267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d351922 q = 0) : d354154 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d351922, d354154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36594 q selected
    | true =>
      simp only [d351922, d354154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d351923 q = 0) : d354155 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d351923, d354155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351923, d354155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352036 q = 0) : d354268 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d352036, d354268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352036, d354268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352037 q = 0) : d354269 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352037, d354269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352037, d354269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352177 q = 0) : d354359 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352177, d354359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352177, d354359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d352265 q = 0) : d354419 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352265, d354419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352265, d354419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro36654 (p : Pattern) (selected : d352270 p = 0) : d354424 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352034 q = 0) : d354266 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352034, d354266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36612 q selected
    | true =>
      simp only [d352034, d354266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352035 q = 0) : d354267 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352035, d354267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352035, d354267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d351922 q = 0) : d354154 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d351922, d354154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36594 q selected
    | true =>
      simp only [d351922, d354154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d351923 q = 0) : d354155 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d351923, d354155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351923, d354155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352036 q = 0) : d354268 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d352036, d354268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352036, d354268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352183 q = 0) : d354365 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352183, d354365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352183, d354365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d352184 q = 0) : d354366 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352184, d354366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352184, d354366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d352270 q = 0) : d354424 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352270, d354424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352270, d354424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro36655 (p : Pattern) (selected : d352274 p = 0) : d354428 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352219 q = 0) : d354401 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352219, d354401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36644 q selected
    | true =>
      simp only [d352219, d354401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352220 q = 0) : d354402 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352220, d354402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352220, d354402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352034 q = 0) : d354266 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352034, d354266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36612 q selected
    | true =>
      simp only [d352034, d354266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352035 q = 0) : d354267 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352035, d354267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352035, d354267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352221 q = 0) : d354403 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d352221, d354403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352221, d354403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352222 q = 0) : d354404 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352222, d354404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352222, d354404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352223 q = 0) : d354405 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352223, d354405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352223, d354405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d352274 q = 0) : d354428 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352274, d354428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352274, d354428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro36656 (p : Pattern) (selected : d352276 p = 0) : d354287 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352247 q = 0) : d354266 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352247, d354266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36649 q selected
    | true =>
      simp only [d352247, d354266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352248 q = 0) : d354267 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352248, d354267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352248, d354267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352063 q = 0) : d354154 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352063, d354154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36617 q selected
    | true =>
      simp only [d352063, d354154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352064 q = 0) : d354155 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352064, d354155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352064, d354155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352249 q = 0) : d354268 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d352249, d354268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352249, d354268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352250 q = 0) : d354269 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352250, d354269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352250, d354269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352251 q = 0) : d354270 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352251, d354270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352251, d354270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d352276 q = 0) : d354287 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352276, d354287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352276, d354287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro36657 (p : Pattern) (selected : d352279 p = 0) : d354431 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352034 q = 0) : d354266 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352034, d354266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36612 q selected
    | true =>
      simp only [d352034, d354266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352035 q = 0) : d354267 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352035, d354267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352035, d354267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352255 q = 0) : d354409 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d352255, d354409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352255, d354409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352256 q = 0) : d354410 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352256, d354410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352256, d354410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352257 q = 0) : d354411 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352257, d354411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352257, d354411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352279 q = 0) : d354431 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352279, d354431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352279, d354431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36658 (p : Pattern) (selected : d352285 p = 0) : d354437 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352179 q = 0) : d354361 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352179, d354361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36638 q selected
    | true =>
      simp only [d352179, d354361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36607 q selected
  have h2 (q : Pattern) (selected : d352180 q = 0) : d354362 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352180, d354362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352180, d354362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352181 q = 0) : d354363 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352181, d354363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352181, d354363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352182 q = 0) : d354364 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d352182, d354364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352182, d354364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352186 q = 0) : d354368 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352186, d354368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36639 q selected
    | true =>
      simp only [d352186, d354368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36608 q selected
  have h6 (q : Pattern) (selected : d352187 q = 0) : d354369 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352187, d354369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352187, d354369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d352188 q = 0) : d354370 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352188, d354370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352188, d354370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d352225 q = 0) : d354407 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352225, d354407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36645 q selected
    | true =>
      simp only [d352225, d354407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36613 q selected
  have h9 (q : Pattern) (selected : d352253 q = 0) : d354272 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352253, d354272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36650 q selected
    | true =>
      simp only [d352253, d354272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36618 q selected
  have h10 (q : Pattern) (selected : d352254 q = 0) : d354408 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352254, d354408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d352254, d354408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d352259 q = 0) : d354413 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352259, d354413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36651 q selected
    | true =>
      simp only [d352259, d354413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d352260 q = 0) : d354414 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352260, d354414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d352260, d354414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d352261 q = 0) : d354415 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352261, d354415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d352261, d354415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d352262 q = 0) : d354416 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d352262, d354416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352262, d354416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d352263 q = 0) : d354417 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d352263, d354417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352263, d354417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d352266 q = 0) : d354420 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352266, d354420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36653 q selected
    | true =>
      simp only [d352266, d354420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36620 q selected
  have h17 (q : Pattern) (selected : d352267 q = 0) : d354421 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352267, d354421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352267, d354421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d352268 q = 0) : d354422 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352268, d354422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d352268, d354422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d352269 q = 0) : d354423 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d352269, d354423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352269, d354423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d352271 q = 0) : d354425 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352271, d354425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36654 q selected
    | true =>
      simp only [d352271, d354425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36621 q selected
  have h21 (q : Pattern) (selected : d352272 q = 0) : d354426 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352272, d354426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352272, d354426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d352273 q = 0) : d354427 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352273, d354427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d352273, d354427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d352275 q = 0) : d354429 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352275, d354429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36655 q selected
    | true =>
      simp only [d352275, d354429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36622 q selected
  have h24 (q : Pattern) (selected : d352277 q = 0) : d354288 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352277, d354288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36656 q selected
    | true =>
      simp only [d352277, d354288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36623 q selected
  have h25 (q : Pattern) (selected : d352278 q = 0) : d354430 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352278, d354430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d352278, d354430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d352280 q = 0) : d354432 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352280, d354432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36657 q selected
    | true =>
      simp only [d352280, d354432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d352281 q = 0) : d354433 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352281, d354433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d352281, d354433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d352282 q = 0) : d354434 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352282, d354434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d352282, d354434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d352283 q = 0) : d354435 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d352283, d354435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d352283, d354435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d352284 q = 0) : d354436 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d352284, d354436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d352284, d354436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d352285 q = 0) : d354437 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d352285, d354437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d352285, d354437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro36659 (p : Pattern) (selected : d352287 p = 0) : d354439 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352040 q = 0) : d354272 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352040, d354272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36613 q selected
    | true =>
      simp only [d352040, d354272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36595 q selected
  have h2 (q : Pattern) (selected : d352162 q = 0) : d354344 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352162, d354344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352162, d354344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352163 q = 0) : d354345 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352163, d354345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352163, d354345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352164 q = 0) : d354346 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d352164, d354346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352164, d354346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352165 q = 0) : d354347 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d352165, d354347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352165, d354347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d351928 q = 0) : d354160 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d351928, d354160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36595 q selected
    | true =>
      simp only [d351928, d354160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d351986 q = 0) : d354218 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d351986, d354218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351986, d354218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d351987 q = 0) : d354219 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d351987, d354219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d351987, d354219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d351988 q = 0) : d354220 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d351988, d354220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351988, d354220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d351989 q = 0) : d354221 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d351989, d354221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351989, d354221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d352287 q = 0) : d354439 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d352287, d354439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352287, d354439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro36660 (p : Pattern) (selected : d352294 p = 0) : d354446 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352275 q = 0) : d354429 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352275, d354429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36655 q selected
    | true =>
      simp only [d352275, d354429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36622 q selected
  have h2 (q : Pattern) (selected : d352277 q = 0) : d354288 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352277, d354288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36656 q selected
    | true =>
      simp only [d352277, d354288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36623 q selected
  have h3 (q : Pattern) (selected : d352278 q = 0) : d354430 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352278, d354430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d352278, d354430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d352280 q = 0) : d354432 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352280, d354432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36657 q selected
    | true =>
      simp only [d352280, d354432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352281 q = 0) : d354433 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352281, d354433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352281, d354433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352282 q = 0) : d354434 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352282, d354434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352282, d354434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d352292 q = 0) : d354444 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d352292, d354444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352292, d354444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d352293 q = 0) : d354445 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d352293, d354445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352293, d354445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d352294 q = 0) : d354446 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d352294, d354446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352294, d354446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro36661 (p : Pattern) (selected : d352296 p = 0) : d354448 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d351935 q = 0) : d354167 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d351935, d354167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36597 q selected
    | true =>
      simp only [d351935, d354167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d351993 q = 0) : d354225 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d351993, d354225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351993, d354225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d351994 q = 0) : d354226 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d351994, d354226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d351994, d354226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d351995 q = 0) : d354227 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d351995, d354227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351995, d354227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d351996 q = 0) : d354228 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d351996, d354228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351996, d354228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352296 q = 0) : d354448 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d352296, d354448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352296, d354448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro36662 (p : Pattern) (selected : d352312 p = 0) : d354464 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352302 q = 0) : d354454 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352302, d354454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352302, d354454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36641 q selected
  have h2 (q : Pattern) (selected : d352199 q = 0) : d354381 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352199, d354381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36641 q selected
    | true =>
      simp only [d352199, d354381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d352303 q = 0) : d354455 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352303, d354455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d352303, d354455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d352200 q = 0) : d354382 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352200, d354382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352200, d354382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352304 q = 0) : d354456 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352304, d354456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352304, d354456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352305 q = 0) : d354457 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d352305, d354457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352305, d354457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352107 q = 0) : d354308 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352107, d354308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352107, d354308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36610 q selected
  have h8 (q : Pattern) (selected : d352022 q = 0) : d354254 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352022, d354254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36610 q selected
    | true =>
      simp only [d352022, d354254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d352108 q = 0) : d354309 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352108, d354309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352108, d354309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d352023 q = 0) : d354255 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352023, d354255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d352023, d354255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d352109 q = 0) : d354310 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352109, d354310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d352109, d354310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d352110 q = 0) : d354311 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d352110, d354311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d352110, d354311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d352306 q = 0) : d354458 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d352306, d354458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352306, d354458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d352307 q = 0) : d354459 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352307, d354459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352307, d354459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36642 q selected
  have h15 (q : Pattern) (selected : d352207 q = 0) : d354389 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352207, d354389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36642 q selected
    | true =>
      simp only [d352207, d354389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d352308 q = 0) : d354460 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352308, d354460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d352308, d354460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d352208 q = 0) : d354390 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352208, d354390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d352208, d354390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d352309 q = 0) : d354461 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352309, d354461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d352309, d354461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d352310 q = 0) : d354462 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d352310, d354462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d352310, d354462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d351951 q = 0) : d354183 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d351951, d354183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351951, d354183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36592 q selected
  have h21 (q : Pattern) (selected : d351910 q = 0) : d354142 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d351910, d354142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36592 q selected
    | true =>
      simp only [d351910, d354142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d351952 q = 0) : d354184 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d351952, d354184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d351952, d354184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d351911 q = 0) : d354143 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d351911, d354143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d351911, d354143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d351953 q = 0) : d354185 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d351953, d354185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d351953, d354185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d351954 q = 0) : d354186 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d351954, d354186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d351954, d354186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d352311 q = 0) : d354463 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d352311, d354463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d352311, d354463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d352312 q = 0) : d354464 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d352312, d354464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d352312, d354464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro36663 (p : Pattern) (selected : d352318 p = 0) : d354470 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352313 q = 0) : d354465 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d352313, d354465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36662 q selected
    | true =>
      simp only [d352313, d354465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36627 q selected
  have h2 (q : Pattern) (selected : d352314 q = 0) : d354466 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d352314, d354466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352314, d354466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352315 q = 0) : d354467 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d352315, d354467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352315, d354467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d352113 q = 0) : d354314 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d352113, d354314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36627 q selected
    | true =>
      simp only [d352113, d354314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36600 q selected
  have h5 (q : Pattern) (selected : d352114 q = 0) : d354315 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d352114, d354315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352114, d354315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352115 q = 0) : d354316 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d352115, d354316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352115, d354316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d352316 q = 0) : d354468 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d352316, d354468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352316, d354468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d351957 q = 0) : d354189 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d351957, d354189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36600 q selected
    | true =>
      simp only [d351957, d354189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d351958 q = 0) : d354190 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d351958, d354190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351958, d354190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d351959 q = 0) : d354191 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d351959, d354191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351959, d354191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d352116 q = 0) : d354317 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d352116, d354317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352116, d354317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d352317 q = 0) : d354469 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d352317, d354469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352317, d354469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d352318 q = 0) : d354470 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d352318, d354470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d352318, d354470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro36664 (p : Pattern) (selected : d352324 p = 0) : d354476 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352319 q = 0) : d354471 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352319, d354471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36663 q selected
    | true =>
      simp only [d352319, d354471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352320 q = 0) : d354472 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352320, d354472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352320, d354472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352119 q = 0) : d354320 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352119, d354320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36628 q selected
    | true =>
      simp only [d352119, d354320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352120 q = 0) : d354321 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352120, d354321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352120, d354321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352321 q = 0) : d354473 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d352321, d354473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352321, d354473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352322 q = 0) : d354474 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352322, d354474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352322, d354474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352323 q = 0) : d354475 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352323, d354475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352323, d354475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d352324 q = 0) : d354476 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352324, d354476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352324, d354476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro36665 (p : Pattern) (selected : d352331 p = 0) : d354313 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352326 q = 0) : d354308 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352326, d354308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352326, d354308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36647 q selected
  have h2 (q : Pattern) (selected : d352235 q = 0) : d354254 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352235, d354254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36647 q selected
    | true =>
      simp only [d352235, d354254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d352327 q = 0) : d354309 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352327, d354309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d352327, d354309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d352236 q = 0) : d354255 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352236, d354255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352236, d354255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352328 q = 0) : d354310 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352328, d354310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352328, d354310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352329 q = 0) : d354311 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d352329, d354311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352329, d354311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352126 q = 0) : d354183 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352126, d354183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352126, d354183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36615 q selected
  have h8 (q : Pattern) (selected : d352051 q = 0) : d354142 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352051, d354142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36615 q selected
    | true =>
      simp only [d352051, d354142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d352127 q = 0) : d354184 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352127, d354184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352127, d354184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d352052 q = 0) : d354143 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352052, d354143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d352052, d354143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d352128 q = 0) : d354185 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352128, d354185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d352128, d354185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d352129 q = 0) : d354186 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d352129, d354186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d352129, d354186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d352330 q = 0) : d354312 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d352330, d354312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352330, d354312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d352130 q = 0) : d354187 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d352130, d354187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d352130, d354187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d352331 q = 0) : d354313 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d352331, d354313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d352331, d354313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro36666 (p : Pattern) (selected : d352337 p = 0) : d354319 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352332 q = 0) : d354314 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d352332, d354314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36665 q selected
    | true =>
      simp only [d352332, d354314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36630 q selected
  have h2 (q : Pattern) (selected : d352333 q = 0) : d354315 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d352333, d354315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352333, d354315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352334 q = 0) : d354316 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d352334, d354316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352334, d354316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d352132 q = 0) : d354189 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d352132, d354189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36630 q selected
    | true =>
      simp only [d352132, d354189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352133 q = 0) : d354190 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d352133, d354190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352133, d354190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352134 q = 0) : d354191 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d352134, d354191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352134, d354191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d352335 q = 0) : d354317 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d352335, d354317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352335, d354317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d352135 q = 0) : d354192 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d352135, d354192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352135, d354192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d352336 q = 0) : d354318 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d352336, d354318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352336, d354318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d352337 q = 0) : d354319 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d352337, d354319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d352337, d354319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro36667 (p : Pattern) (selected : d352343 p = 0) : d354325 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352338 q = 0) : d354320 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352338, d354320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36666 q selected
    | true =>
      simp only [d352338, d354320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352339 q = 0) : d354321 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352339, d354321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352339, d354321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352138 q = 0) : d354195 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352138, d354195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36631 q selected
    | true =>
      simp only [d352138, d354195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352139 q = 0) : d354196 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352139, d354196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352139, d354196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352340 q = 0) : d354322 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d352340, d354322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352340, d354322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352341 q = 0) : d354323 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352341, d354323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352341, d354323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352342 q = 0) : d354324 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352342, d354324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352342, d354324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d352343 q = 0) : d354325 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352343, d354325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352343, d354325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro36668 (p : Pattern) (selected : d352349 p = 0) : d354482 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352119 q = 0) : d354320 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352119, d354320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36628 q selected
    | true =>
      simp only [d352119, d354320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352120 q = 0) : d354321 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352120, d354321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352120, d354321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352346 q = 0) : d354479 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d352346, d354479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352346, d354479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352347 q = 0) : d354480 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352347, d354480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352347, d354480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352348 q = 0) : d354481 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352348, d354481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352348, d354481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352349 q = 0) : d354482 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352349, d354482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352349, d354482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36669 (p : Pattern) (selected : d352355 p = 0) : d354488 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352325 q = 0) : d354477 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352325, d354477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36664 q selected
    | true =>
      simp only [d352325, d354477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36629 q selected
  have h2 (q : Pattern) (selected : d352344 q = 0) : d354326 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352344, d354326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36667 q selected
    | true =>
      simp only [d352344, d354326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36632 q selected
  have h3 (q : Pattern) (selected : d352345 q = 0) : d354478 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352345, d354478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d352345, d354478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d352350 q = 0) : d354483 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352350, d354483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36668 q selected
    | true =>
      simp only [d352350, d354483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352351 q = 0) : d354484 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352351, d354484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352351, d354484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352352 q = 0) : d354485 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352352, d354485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352352, d354485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d352353 q = 0) : d354486 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d352353, d354486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352353, d354486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d352354 q = 0) : d354487 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d352354, d354487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352354, d354487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d352355 q = 0) : d354488 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d352355, d354488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352355, d354488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro36670 (p : Pattern) (selected : d352361 p = 0) : d354494 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d351969 q = 0) : d354201 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d351969, d354201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36602 q selected
    | true =>
      simp only [d351969, d354201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352357 q = 0) : d354490 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352357, d354490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352357, d354490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352358 q = 0) : d354491 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352358, d354491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352358, d354491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352359 q = 0) : d354492 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d352359, d354492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352359, d354492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352360 q = 0) : d354493 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d352360, d354493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352360, d354493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352361 q = 0) : d354494 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d352361, d354494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352361, d354494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro36671 (p : Pattern) (selected : d352367 p = 0) : d354500 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352167 q = 0) : d354349 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d352167, d354349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352167, d354349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36636 q selected
  have h2 (q : Pattern) (selected : d352168 q = 0) : d354350 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d352168, d354350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d352168, d354350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d352174 q = 0) : d354356 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d352174, d354356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36636 q selected
    | true =>
      simp only [d352174, d354356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36637 q selected
  have h4 (q : Pattern) (selected : d352175 q = 0) : d354357 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d352175, d354357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352175, d354357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352176 q = 0) : d354358 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d352176, d354358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352176, d354358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352286 q = 0) : d354438 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d352286, d354438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36652 q selected
    | true =>
      simp only [d352286, d354438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36658 q selected
  have h7 (q : Pattern) (selected : d352288 q = 0) : d354440 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d352288, d354440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36659 q selected
    | true =>
      simp only [d352288, d354440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36606 q selected
  have h8 (q : Pattern) (selected : d352289 q = 0) : d354441 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d352289, d354441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352289, d354441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d352290 q = 0) : d354442 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d352290, d354442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d352290, d354442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d352291 q = 0) : d354443 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d352291, d354443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352291, d354443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d352295 q = 0) : d354447 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d352295, d354447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352295, d354447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36660 q selected
  have h12 (q : Pattern) (selected : d352297 q = 0) : d354449 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d352297, d354449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352297, d354449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36661 q selected
  have h13 (q : Pattern) (selected : d352298 q = 0) : d354450 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d352298, d354450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d352298, d354450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d352299 q = 0) : d354451 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d352299, d354451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d352299, d354451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d352300 q = 0) : d354452 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d352300, d354452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d352300, d354452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d352301 q = 0) : d354453 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d352301, d354453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d352301, d354453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d352356 q = 0) : d354489 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d352356, d354489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352356, d354489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36669 q selected
  have h18 (q : Pattern) (selected : d352362 q = 0) : d354495 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d352362, d354495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352362, d354495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36670 q selected
  have h19 (q : Pattern) (selected : d352363 q = 0) : d354496 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d352363, d354496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d352363, d354496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d352364 q = 0) : d354497 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d352364, d354497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d352364, d354497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d352365 q = 0) : d354498 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d352365, d354498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d352365, d354498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d352366 q = 0) : d354499 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d352366, d354499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d352366, d354499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d352367 q = 0) : d354500 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d352367, d354500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d352367, d354500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro36672 (p : Pattern) (selected : d352373 p = 0) : d354506 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352368 q = 0) : d354501 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d352368, d354501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352368, d354501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36671 q selected
  have h2 (q : Pattern) (selected : d352369 q = 0) : d354502 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d352369, d354502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352369, d354502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352370 q = 0) : d354503 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d352370, d354503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352370, d354503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d352371 q = 0) : d354504 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d352371, d354504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352371, d354504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352372 q = 0) : d354505 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d352372, d354505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352372, d354505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352373 q = 0) : d354506 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d352373, d354506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352373, d354506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro36673 (p : Pattern) (selected : d352377 p = 0) : d354510 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352213 q = 0) : d354395 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d352213, d354395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36643 q selected
    | true =>
      simp only [d352213, d354395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36611 q selected
  have h2 (q : Pattern) (selected : d352214 q = 0) : d354396 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d352214, d354396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352214, d354396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352215 q = 0) : d354397 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d352215, d354397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352215, d354397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d352028 q = 0) : d354260 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d352028, d354260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36611 q selected
    | true =>
      simp only [d352028, d354260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36593 q selected
  have h5 (q : Pattern) (selected : d352029 q = 0) : d354261 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d352029, d354261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352029, d354261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352030 q = 0) : d354262 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d352030, d354262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352030, d354262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d352216 q = 0) : d354398 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d352216, d354398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352216, d354398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d352375 q = 0) : d354508 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d352375, d354508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352375, d354508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d352376 q = 0) : d354509 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d352376, d354509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352376, d354509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d352377 q = 0) : d354510 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d352377, d354510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d352377, d354510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro36674 (p : Pattern) (selected : d352381 p = 0) : d354514 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352028 q = 0) : d354260 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d352028, d354260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36611 q selected
    | true =>
      simp only [d352028, d354260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36593 q selected
  have h2 (q : Pattern) (selected : d352029 q = 0) : d354261 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d352029, d354261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352029, d354261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352030 q = 0) : d354262 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d352030, d354262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352030, d354262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d352375 q = 0) : d354508 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d352375, d354508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352375, d354508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352380 q = 0) : d354513 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d352380, d354513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352380, d354513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352381 q = 0) : d354514 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d352381, d354514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352381, d354514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36675 (p : Pattern) (selected : d352387 p = 0) : d354520 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352378 q = 0) : d354511 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352378, d354511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36673 q selected
    | true =>
      simp only [d352378, d354511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352379 q = 0) : d354512 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352379, d354512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352379, d354512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352382 q = 0) : d354515 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352382, d354515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36674 q selected
    | true =>
      simp only [d352382, d354515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352383 q = 0) : d354516 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352383, d354516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352383, d354516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352384 q = 0) : d354517 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d352384, d354517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352384, d354517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352385 q = 0) : d354518 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352385, d354518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352385, d354518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352386 q = 0) : d354519 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352386, d354519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352386, d354519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d352387 q = 0) : d354520 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352387, d354520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352387, d354520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro36676 (p : Pattern) (selected : d352391 p = 0) : d354524 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352382 q = 0) : d354515 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352382, d354515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36674 q selected
    | true =>
      simp only [d352382, d354515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352383 q = 0) : d354516 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352383, d354516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352383, d354516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352388 q = 0) : d354521 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d352388, d354521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352388, d354521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352389 q = 0) : d354522 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352389, d354522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352389, d354522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352390 q = 0) : d354523 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352390, d354523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352390, d354523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352391 q = 0) : d354524 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352391, d354524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352391, d354524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro36677 (p : Pattern) (selected : d352397 p = 0) : d354530 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352392 q = 0) : d354525 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352392, d354525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36675 q selected
    | true =>
      simp only [d352392, d354525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36676 q selected
  have h2 (q : Pattern) (selected : d352393 q = 0) : d354526 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352393, d354526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352393, d354526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352394 q = 0) : d354527 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352394, d354527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352394, d354527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352395 q = 0) : d354528 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d352395, d354528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352395, d354528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352396 q = 0) : d354529 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d352396, d354529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352396, d354529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352397 q = 0) : d354530 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d352397, d354530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352397, d354530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro36678 (p : Pattern) (selected : d352400 p = 0) : d354533 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352378 q = 0) : d354511 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352378, d354511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36673 q selected
    | true =>
      simp only [d352378, d354511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352379 q = 0) : d354512 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352379, d354512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352379, d354512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352382 q = 0) : d354515 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352382, d354515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36674 q selected
    | true =>
      simp only [d352382, d354515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352383 q = 0) : d354516 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352383, d354516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352383, d354516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352384 q = 0) : d354517 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d352384, d354517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352384, d354517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352385 q = 0) : d354518 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352385, d354518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352385, d354518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352386 q = 0) : d354519 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352386, d354519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352386, d354519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d352400 q = 0) : d354533 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352400, d354533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352400, d354533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro36679 (p : Pattern) (selected : d352401 p = 0) : d354534 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352382 q = 0) : d354515 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352382, d354515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36674 q selected
    | true =>
      simp only [d352382, d354515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352383 q = 0) : d354516 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352383, d354516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352383, d354516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352388 q = 0) : d354521 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d352388, d354521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352388, d354521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352389 q = 0) : d354522 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352389, d354522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352389, d354522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352390 q = 0) : d354523 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352390, d354523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352390, d354523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352401 q = 0) : d354534 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352401, d354534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352401, d354534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36680 (p : Pattern) (selected : d352407 p = 0) : d354540 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352392 q = 0) : d354525 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352392, d354525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36675 q selected
    | true =>
      simp only [d352392, d354525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36676 q selected
  have h2 (q : Pattern) (selected : d352393 q = 0) : d354526 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352393, d354526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352393, d354526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352394 q = 0) : d354527 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352394, d354527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352394, d354527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352395 q = 0) : d354528 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d352395, d354528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352395, d354528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352396 q = 0) : d354529 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d352396, d354529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352396, d354529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352402 q = 0) : d354535 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352402, d354535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36678 q selected
    | true =>
      simp only [d352402, d354535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36679 q selected
  have h7 (q : Pattern) (selected : d352403 q = 0) : d354536 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352403, d354536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352403, d354536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d352404 q = 0) : d354537 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352404, d354537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352404, d354537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d352405 q = 0) : d354538 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d352405, d354538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352405, d354538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d352406 q = 0) : d354539 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d352406, d354539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352406, d354539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d352407 q = 0) : d354540 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d352407, d354540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352407, d354540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro36681 (p : Pattern) (selected : d352412 p = 0) : d354545 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352378 q = 0) : d354511 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352378, d354511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36673 q selected
    | true =>
      simp only [d352378, d354511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352379 q = 0) : d354512 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352379, d354512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352379, d354512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352382 q = 0) : d354515 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352382, d354515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36674 q selected
    | true =>
      simp only [d352382, d354515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352383 q = 0) : d354516 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352383, d354516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352383, d354516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352384 q = 0) : d354517 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d352384, d354517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352384, d354517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352385 q = 0) : d354518 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352385, d354518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352385, d354518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352411 q = 0) : d354544 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352411, d354544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352411, d354544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d352412 q = 0) : d354545 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352412, d354545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352412, d354545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro36682 (p : Pattern) (selected : d352414 p = 0) : d354547 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352382 q = 0) : d354515 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352382, d354515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36674 q selected
    | true =>
      simp only [d352382, d354515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352383 q = 0) : d354516 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352383, d354516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352383, d354516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352388 q = 0) : d354521 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d352388, d354521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352388, d354521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352389 q = 0) : d354522 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352389, d354522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352389, d354522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352413 q = 0) : d354546 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352413, d354546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352413, d354546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352414 q = 0) : d354547 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352414, d354547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352414, d354547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro36683 (p : Pattern) (selected : d352421 p = 0) : d354554 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352378 q = 0) : d354511 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352378, d354511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36673 q selected
    | true =>
      simp only [d352378, d354511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352379 q = 0) : d354512 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352379, d354512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352379, d354512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352382 q = 0) : d354515 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352382, d354515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36674 q selected
    | true =>
      simp only [d352382, d354515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352383 q = 0) : d354516 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352383, d354516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352383, d354516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352384 q = 0) : d354517 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d352384, d354517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352384, d354517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352419 q = 0) : d354552 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352419, d354552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352419, d354552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d352420 q = 0) : d354553 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352420, d354553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352420, d354553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d352421 q = 0) : d354554 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352421, d354554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352421, d354554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro36684 (p : Pattern) (selected : d352424 p = 0) : d354557 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352382 q = 0) : d354515 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352382, d354515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36674 q selected
    | true =>
      simp only [d352382, d354515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352383 q = 0) : d354516 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352383, d354516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352383, d354516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352388 q = 0) : d354521 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d352388, d354521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352388, d354521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352422 q = 0) : d354555 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352422, d354555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352422, d354555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352423 q = 0) : d354556 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352423, d354556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352423, d354556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352424 q = 0) : d354557 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352424, d354557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352424, d354557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro36685 (p : Pattern) (selected : d352429 p = 0) : d354562 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1 q = 0) : d0 q = 1 := by
    change (1 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d253269 q = 0) : d253268 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d253269, d253268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d253269, d253268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d352190 q = 0) : d354372 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d352190, d354372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352190, d354372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d352428 q = 0) : d354561 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d352428, d354561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352428, d354561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352429 q = 0) : d354562 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d352429, d354562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352429, d354562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro36686 (p : Pattern) (selected : d352436 p = 0) : d354569 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1 q = 0) : d0 q = 1 := by
    change (1 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d253268 q = 0) : d253269 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d253268, d253269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253268, d253269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352189 q = 0) : d354371 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d352189, d354371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352189, d354371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d352433 q = 0) : d354566 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d352433, d354566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352433, d354566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352434 q = 0) : d354567 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d352434, d354567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352434, d354567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352435 q = 0) : d354568 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d352435, d354568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352435, d354568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352436 q = 0) : d354569 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d352436, d354569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352436, d354569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro36687 (p : Pattern) (selected : d352442 p = 0) : d354575 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352430 q = 0) : d354563 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d352430, d354563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36685 q selected
    | true =>
      simp only [d352430, d354563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352431 q = 0) : d354564 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d352431, d354564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d352431, d354564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d352193 q = 0) : d354375 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d352193, d354375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36640 q selected
    | true =>
      simp only [d352193, d354375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352194 q = 0) : d354376 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d352194, d354376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352194, d354376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352432 q = 0) : d354565 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d352432, d354565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352432, d354565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352437 q = 0) : d354570 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d352437, d354570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36686 q selected
    | true =>
      simp only [d352437, d354570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352438 q = 0) : d354571 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d352438, d354571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352438, d354571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d352016 q = 0) : d354248 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d352016, d354248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36609 q selected
    | true =>
      simp only [d352016, d354248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d352017 q = 0) : d354249 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d352017, d354249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d352017, d354249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d352439 q = 0) : d354572 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d352439, d354572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352439, d354572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d352440 q = 0) : d354573 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d352440, d354573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352440, d354573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d352441 q = 0) : d354574 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d352441, d354574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d352441, d354574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d352195 q = 0) : d354377 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d352195, d354377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352195, d354377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h14 (q : Pattern) (selected : d351904 q = 0) : d354136 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d351904, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36591 q selected
    | true =>
      simp only [d351904, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d351905 q = 0) : d354137 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d351905, d354137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d351905, d354137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d352018 q = 0) : d354250 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d352018, d354250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d352018, d354250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d352196 q = 0) : d354378 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d352196, d354378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d352196, d354378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d352197 q = 0) : d354379 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d352197, d354379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d352197, d354379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d352442 q = 0) : d354575 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d352442, d354575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d352442, d354575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro36688 (p : Pattern) (selected : d352447 p = 0) : d354580 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352193 q = 0) : d354375 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d352193, d354375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36640 q selected
    | true =>
      simp only [d352193, d354375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352194 q = 0) : d354376 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d352194, d354376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d352194, d354376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d352016 q = 0) : d354248 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d352016, d354248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36609 q selected
    | true =>
      simp only [d352016, d354248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352017 q = 0) : d354249 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d352017, d354249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352017, d354249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352195 q = 0) : d354377 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d352195, d354377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352195, d354377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d351904 q = 0) : d354136 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d351904, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36591 q selected
    | true =>
      simp only [d351904, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d351905 q = 0) : d354137 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d351905, d354137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d351905, d354137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d352018 q = 0) : d354250 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d352018, d354250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352018, d354250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d352196 q = 0) : d354378 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d352196, d354378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352196, d354378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d352197 q = 0) : d354379 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d352197, d354379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d352197, d354379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d352204 q = 0) : d354386 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d352204, d354386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d352204, d354386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d352205 q = 0) : d354387 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d352205, d354387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d352205, d354387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d352447 q = 0) : d354580 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d352447, d354580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d352447, d354580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro36689 (p : Pattern) (selected : d352455 p = 0) : d354588 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352193 q = 0) : d354375 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d352193, d354375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36640 q selected
    | true =>
      simp only [d352193, d354375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352194 q = 0) : d354376 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d352194, d354376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d352194, d354376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d352016 q = 0) : d354248 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d352016, d354248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36609 q selected
    | true =>
      simp only [d352016, d354248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352017 q = 0) : d354249 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d352017, d354249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352017, d354249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352195 q = 0) : d354377 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d352195, d354377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352195, d354377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352453 q = 0) : d354586 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d352453, d354586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352453, d354586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352454 q = 0) : d354587 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d352454, d354587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352454, d354587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d351904 q = 0) : d354136 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d351904, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36591 q selected
    | true =>
      simp only [d351904, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d351905 q = 0) : d354137 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d351905, d354137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d351905, d354137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d352018 q = 0) : d354250 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d352018, d354250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352018, d354250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d352204 q = 0) : d354386 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d352204, d354386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d352204, d354386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d352205 q = 0) : d354387 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d352205, d354387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d352205, d354387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d352455 q = 0) : d354588 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d352455, d354588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352455, d354588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro36690 (p : Pattern) (selected : d352461 p = 0) : d354594 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352443 q = 0) : d354576 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352443, d354576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36687 q selected
    | true =>
      simp only [d352443, d354576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352444 q = 0) : d354577 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352444, d354577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d352444, d354577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d352445 q = 0) : d354578 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352445, d354578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352445, d354578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d352446 q = 0) : d354579 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d352446, d354579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352446, d354579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352448 q = 0) : d354581 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352448, d354581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36688 q selected
    | true =>
      simp only [d352448, d354581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352449 q = 0) : d354582 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352449, d354582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352449, d354582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352450 q = 0) : d354583 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352450, d354583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352450, d354583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d352451 q = 0) : d354584 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d352451, d354584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352451, d354584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d352452 q = 0) : d354585 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d352452, d354585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352452, d354585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d352456 q = 0) : d354589 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352456, d354589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36689 q selected
    | true =>
      simp only [d352456, d354589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d352457 q = 0) : d354590 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352457, d354590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d352457, d354590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d352458 q = 0) : d354591 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352458, d354591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352458, d354591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d352459 q = 0) : d354592 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d352459, d354592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d352459, d354592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d352207 q = 0) : d354389 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352207, d354389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36642 q selected
    | true =>
      simp only [d352207, d354389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d352208 q = 0) : d354390 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352208, d354390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d352208, d354390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d352209 q = 0) : d354391 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352209, d354391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352209, d354391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d352210 q = 0) : d354392 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d352210, d354392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d352210, d354392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d352460 q = 0) : d354593 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d352460, d354593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d352460, d354593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d352461 q = 0) : d354594 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d352461, d354594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d352461, d354594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro36691 (p : Pattern) (selected : d352465 p = 0) : d354598 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352207 q = 0) : d354389 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352207, d354389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36642 q selected
    | true =>
      simp only [d352207, d354389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352208 q = 0) : d354390 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352208, d354390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d352208, d354390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d352209 q = 0) : d354391 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352209, d354391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352209, d354391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d352210 q = 0) : d354392 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d352210, d354392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352210, d354392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d351910 q = 0) : d354142 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d351910, d354142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36592 q selected
    | true =>
      simp only [d351910, d354142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d351911 q = 0) : d354143 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d351911, d354143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d351911, d354143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d351912 q = 0) : d354144 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d351912, d354144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351912, d354144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d351913 q = 0) : d354145 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d351913, d354145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d351913, d354145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d352211 q = 0) : d354393 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d352211, d354393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352211, d354393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d351914 q = 0) : d354146 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d351914, d354146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d351914, d354146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d352465 q = 0) : d354598 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d352465, d354598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d352465, d354598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro36692 (p : Pattern) (selected : d352471 p = 0) : d354604 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352462 q = 0) : d354595 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d352462, d354595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36690 q selected
    | true =>
      simp only [d352462, d354595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36643 q selected
  have h2 (q : Pattern) (selected : d352463 q = 0) : d354596 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d352463, d354596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352463, d354596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352464 q = 0) : d354597 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d352464, d354597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352464, d354597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d352466 q = 0) : d354599 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d352466, d354599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36643 q selected
    | true =>
      simp only [d352466, d354599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36691 q selected
  have h5 (q : Pattern) (selected : d352467 q = 0) : d354600 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d352467, d354600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352467, d354600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352468 q = 0) : d354601 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d352468, d354601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352468, d354601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d352469 q = 0) : d354602 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d352469, d354602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352469, d354602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d352213 q = 0) : d354395 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d352213, d354395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36643 q selected
    | true =>
      simp only [d352213, d354395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36611 q selected
  have h9 (q : Pattern) (selected : d352214 q = 0) : d354396 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d352214, d354396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352214, d354396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d352215 q = 0) : d354397 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d352215, d354397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352215, d354397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d352028 q = 0) : d354260 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d352028, d354260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36611 q selected
    | true =>
      simp only [d352028, d354260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36593 q selected
  have h12 (q : Pattern) (selected : d352029 q = 0) : d354261 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d352029, d354261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352029, d354261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d352030 q = 0) : d354262 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d352030, d354262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352030, d354262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d352216 q = 0) : d354398 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d352216, d354398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d352216, d354398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d352470 q = 0) : d354603 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d352470, d354603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352470, d354603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d352471 q = 0) : d354604 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d352471, d354604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d352471, d354604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro36693 (p : Pattern) (selected : d352477 p = 0) : d354610 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352472 q = 0) : d354605 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352472, d354605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36692 q selected
    | true =>
      simp only [d352472, d354605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352473 q = 0) : d354606 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352473, d354606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352473, d354606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352378 q = 0) : d354511 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352378, d354511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36673 q selected
    | true =>
      simp only [d352378, d354511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352379 q = 0) : d354512 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352379, d354512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352379, d354512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352474 q = 0) : d354607 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d352474, d354607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352474, d354607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352475 q = 0) : d354608 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352475, d354608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352475, d354608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352476 q = 0) : d354609 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352476, d354609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352476, d354609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d352477 q = 0) : d354610 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352477, d354610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352477, d354610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro36694 (p : Pattern) (selected : d352482 p = 0) : d354374 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2 q = 0) : d0 q = 1 := by
    change (2 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d351450 q = 0) : d253269 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d351450, d253269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351450, d253269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352479 q = 0) : d354371 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d352479, d354371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352479, d354371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d352041 q = 0) : d253268 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d352041, d253268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d352041, d253268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352480 q = 0) : d354372 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d352480, d354372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352480, d354372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352481 q = 0) : d354373 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d352481, d354373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352481, d354373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d352226 q = 0) : d354245 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d352226, d354245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352226, d354245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h8 (q : Pattern) (selected : d352042 q = 0) : d354133 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d352042, d354133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352042, d354133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d352227 q = 0) : d354246 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d352227, d354246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352227, d354246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d352482 q = 0) : d354374 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d352482, d354374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352482, d354374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro36695 (p : Pattern) (selected : d352488 p = 0) : d354380 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352483 q = 0) : d354375 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d352483, d354375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36694 q selected
    | true =>
      simp only [d352483, d354375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352484 q = 0) : d354376 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d352484, d354376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d352484, d354376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d352229 q = 0) : d354248 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d352229, d354248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36646 q selected
    | true =>
      simp only [d352229, d354248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352230 q = 0) : d354249 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d352230, d354249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352230, d354249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352485 q = 0) : d354377 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d352485, d354377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352485, d354377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352045 q = 0) : d354136 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d352045, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36614 q selected
    | true =>
      simp only [d352045, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352046 q = 0) : d354137 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d352046, d354137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352046, d354137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d352231 q = 0) : d354250 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d352231, d354250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352231, d354250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d352486 q = 0) : d354378 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d352486, d354378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352486, d354378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d352487 q = 0) : d354379 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d352487, d354379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d352487, d354379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d352047 q = 0) : d354138 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d352047, d354138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352047, d354138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d352232 q = 0) : d354251 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d352232, d354251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d352232, d354251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d352233 q = 0) : d354252 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d352233, d354252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d352233, d354252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d352488 q = 0) : d354380 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d352488, d354380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d352488, d354380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro36696 (p : Pattern) (selected : d352496 p = 0) : d354388 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352229 q = 0) : d354248 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d352229, d354248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36646 q selected
    | true =>
      simp only [d352229, d354248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352230 q = 0) : d354249 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d352230, d354249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d352230, d354249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d352045 q = 0) : d354136 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d352045, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36614 q selected
    | true =>
      simp only [d352045, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352046 q = 0) : d354137 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d352046, d354137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352046, d354137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352231 q = 0) : d354250 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d352231, d354250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352231, d354250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352494 q = 0) : d354386 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d352494, d354386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352494, d354386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352495 q = 0) : d354387 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d352495, d354387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352495, d354387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d352047 q = 0) : d354138 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d352047, d354138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352047, d354138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d352048 q = 0) : d354139 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d352048, d354139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d352048, d354139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d352049 q = 0) : d354140 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d352049, d354140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d352049, d354140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d352496 q = 0) : d354388 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d352496, d354388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352496, d354388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro36697 (p : Pattern) (selected : d352502 p = 0) : d354394 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352489 q = 0) : d354381 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352489, d354381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36695 q selected
    | true =>
      simp only [d352489, d354381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352490 q = 0) : d354382 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352490, d354382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d352490, d354382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d352491 q = 0) : d354383 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352491, d354383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352491, d354383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d352492 q = 0) : d354384 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d352492, d354384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352492, d354384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352235 q = 0) : d354254 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352235, d354254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36647 q selected
    | true =>
      simp only [d352235, d354254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352236 q = 0) : d354255 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352236, d354255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352236, d354255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352237 q = 0) : d354256 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352237, d354256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352237, d354256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d352238 q = 0) : d354257 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d352238, d354257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352238, d354257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d352493 q = 0) : d354385 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d352493, d354385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352493, d354385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d352497 q = 0) : d354389 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352497, d354389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36696 q selected
    | true =>
      simp only [d352497, d354389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d352498 q = 0) : d354390 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352498, d354390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d352498, d354390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d352499 q = 0) : d354391 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352499, d354391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352499, d354391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d352500 q = 0) : d354392 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d352500, d354392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d352500, d354392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d352051 q = 0) : d354142 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352051, d354142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36615 q selected
    | true =>
      simp only [d352051, d354142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d352052 q = 0) : d354143 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352052, d354143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d352052, d354143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d352053 q = 0) : d354144 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352053, d354144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352053, d354144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d352054 q = 0) : d354145 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d352054, d354145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d352054, d354145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d352501 q = 0) : d354393 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d352501, d354393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d352501, d354393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d352502 q = 0) : d354394 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d352502, d354394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d352502, d354394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro36698 (p : Pattern) (selected : d352509 p = 0) : d354510 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352503 q = 0) : d354395 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d352503, d354395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36697 q selected
    | true =>
      simp only [d352503, d354395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36648 q selected
  have h2 (q : Pattern) (selected : d352504 q = 0) : d354396 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d352504, d354396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352504, d354396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352505 q = 0) : d354397 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d352505, d354397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352505, d354397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d352241 q = 0) : d354260 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d352241, d354260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36648 q selected
    | true =>
      simp only [d352241, d354260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36616 q selected
  have h5 (q : Pattern) (selected : d352242 q = 0) : d354261 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d352242, d354261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352242, d354261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352243 q = 0) : d354262 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d352243, d354262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352243, d354262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d352506 q = 0) : d354398 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d352506, d354398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352506, d354398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d352507 q = 0) : d354508 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d352507, d354508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352507, d354508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d352508 q = 0) : d354509 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d352508, d354509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352508, d354509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d352509 q = 0) : d354510 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d352509, d354510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d352509, d354510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro36699 (p : Pattern) (selected : d352513 p = 0) : d354514 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352241 q = 0) : d354260 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d352241, d354260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36648 q selected
    | true =>
      simp only [d352241, d354260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36616 q selected
  have h2 (q : Pattern) (selected : d352242 q = 0) : d354261 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d352242, d354261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352242, d354261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352243 q = 0) : d354262 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d352243, d354262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352243, d354262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d352507 q = 0) : d354508 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d352507, d354508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352507, d354508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352512 q = 0) : d354513 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d352512, d354513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352512, d354513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352513 q = 0) : d354514 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d352513, d354514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352513, d354514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36700 (p : Pattern) (selected : d352519 p = 0) : d354520 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352510 q = 0) : d354511 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352510, d354511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36698 q selected
    | true =>
      simp only [d352510, d354511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352511 q = 0) : d354512 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352511, d354512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352511, d354512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352514 q = 0) : d354515 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352514, d354515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36699 q selected
    | true =>
      simp only [d352514, d354515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352515 q = 0) : d354516 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352515, d354516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352515, d354516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352516 q = 0) : d354517 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d352516, d354517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352516, d354517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352517 q = 0) : d354518 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352517, d354518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352517, d354518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352518 q = 0) : d354519 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352518, d354519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352518, d354519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d352519 q = 0) : d354520 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352519, d354520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352519, d354520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro36701 (p : Pattern) (selected : d352523 p = 0) : d354524 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352514 q = 0) : d354515 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352514, d354515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36699 q selected
    | true =>
      simp only [d352514, d354515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352515 q = 0) : d354516 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352515, d354516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352515, d354516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352520 q = 0) : d354521 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d352520, d354521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352520, d354521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352521 q = 0) : d354522 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352521, d354522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352521, d354522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352522 q = 0) : d354523 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352522, d354523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352522, d354523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352523 q = 0) : d354524 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352523, d354524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352523, d354524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro36702 (p : Pattern) (selected : d352529 p = 0) : d354616 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352378 q = 0) : d354511 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352378, d354511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36673 q selected
    | true =>
      simp only [d352378, d354511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352379 q = 0) : d354512 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352379, d354512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352379, d354512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352526 q = 0) : d354613 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d352526, d354613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352526, d354613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352527 q = 0) : d354614 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352527, d354614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352527, d354614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352528 q = 0) : d354615 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352528, d354615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352528, d354615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352529 q = 0) : d354616 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352529, d354616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352529, d354616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro36703 (p : Pattern) (selected : d352535 p = 0) : d354622 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352415 q = 0) : d354548 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352415, d354548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36681 q selected
    | true =>
      simp only [d352415, d354548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36682 q selected
  have h2 (q : Pattern) (selected : d352416 q = 0) : d354549 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352416, d354549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352416, d354549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352417 q = 0) : d354550 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352417, d354550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352417, d354550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352418 q = 0) : d354551 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d352418, d354551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352418, d354551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352425 q = 0) : d354558 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352425, d354558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36683 q selected
    | true =>
      simp only [d352425, d354558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36684 q selected
  have h6 (q : Pattern) (selected : d352426 q = 0) : d354559 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352426, d354559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352426, d354559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d352427 q = 0) : d354560 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352427, d354560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352427, d354560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d352478 q = 0) : d354611 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352478, d354611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36693 q selected
    | true =>
      simp only [d352478, d354611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36675 q selected
  have h9 (q : Pattern) (selected : d352524 q = 0) : d354525 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352524, d354525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36700 q selected
    | true =>
      simp only [d352524, d354525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36701 q selected
  have h10 (q : Pattern) (selected : d352525 q = 0) : d354612 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352525, d354612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d352525, d354612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d352530 q = 0) : d354617 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352530, d354617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36702 q selected
    | true =>
      simp only [d352530, d354617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d352531 q = 0) : d354618 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352531, d354618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d352531, d354618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d352532 q = 0) : d354619 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352532, d354619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d352532, d354619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d352533 q = 0) : d354620 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d352533, d354620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352533, d354620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d352534 q = 0) : d354621 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d352534, d354621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352534, d354621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d352535 q = 0) : d354622 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d352535, d354622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352535, d354622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro36704 (p : Pattern) (selected : d352536 p = 0) : d354623 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352378 q = 0) : d354511 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352378, d354511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36673 q selected
    | true =>
      simp only [d352378, d354511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352379 q = 0) : d354512 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352379, d354512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352379, d354512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352382 q = 0) : d354515 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352382, d354515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36674 q selected
    | true =>
      simp only [d352382, d354515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352383 q = 0) : d354516 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352383, d354516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352383, d354516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352384 q = 0) : d354517 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d352384, d354517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352384, d354517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352385 q = 0) : d354518 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352385, d354518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352385, d354518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352411 q = 0) : d354544 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352411, d354544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352411, d354544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d352536 q = 0) : d354623 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352536, d354623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352536, d354623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro36705 (p : Pattern) (selected : d352537 p = 0) : d354624 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352382 q = 0) : d354515 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352382, d354515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36674 q selected
    | true =>
      simp only [d352382, d354515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352383 q = 0) : d354516 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352383, d354516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352383, d354516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352388 q = 0) : d354521 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d352388, d354521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352388, d354521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352389 q = 0) : d354522 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352389, d354522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352389, d354522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352413 q = 0) : d354546 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352413, d354546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352413, d354546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352537 q = 0) : d354624 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352537, d354624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352537, d354624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36706 (p : Pattern) (selected : d352542 p = 0) : d354629 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352378 q = 0) : d354511 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352378, d354511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36673 q selected
    | true =>
      simp only [d352378, d354511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352379 q = 0) : d354512 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352379, d354512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352379, d354512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352382 q = 0) : d354515 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352382, d354515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36674 q selected
    | true =>
      simp only [d352382, d354515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352383 q = 0) : d354516 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352383, d354516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352383, d354516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352384 q = 0) : d354517 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d352384, d354517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352384, d354517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352419 q = 0) : d354552 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352419, d354552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352419, d354552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d352420 q = 0) : d354553 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352420, d354553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352420, d354553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d352542 q = 0) : d354629 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352542, d354629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352542, d354629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro36707 (p : Pattern) (selected : d352543 p = 0) : d354630 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352382 q = 0) : d354515 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352382, d354515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36674 q selected
    | true =>
      simp only [d352382, d354515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352383 q = 0) : d354516 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352383, d354516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352383, d354516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352388 q = 0) : d354521 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d352388, d354521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352388, d354521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352422 q = 0) : d354555 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352422, d354555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352422, d354555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352423 q = 0) : d354556 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352423, d354556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352423, d354556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352543 q = 0) : d354630 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352543, d354630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352543, d354630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36708 (p : Pattern) (selected : d352547 p = 0) : d354634 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352472 q = 0) : d354605 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352472, d354605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36692 q selected
    | true =>
      simp only [d352472, d354605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352473 q = 0) : d354606 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352473, d354606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352473, d354606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352378 q = 0) : d354511 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352378, d354511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36673 q selected
    | true =>
      simp only [d352378, d354511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352379 q = 0) : d354512 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352379, d354512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352379, d354512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352474 q = 0) : d354607 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d352474, d354607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352474, d354607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352475 q = 0) : d354608 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352475, d354608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352475, d354608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352476 q = 0) : d354609 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352476, d354609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352476, d354609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d352547 q = 0) : d354634 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352547, d354634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352547, d354634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro36709 (p : Pattern) (selected : d352549 p = 0) : d354533 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352510 q = 0) : d354511 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352510, d354511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36698 q selected
    | true =>
      simp only [d352510, d354511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352511 q = 0) : d354512 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352511, d354512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352511, d354512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352514 q = 0) : d354515 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352514, d354515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36699 q selected
    | true =>
      simp only [d352514, d354515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352515 q = 0) : d354516 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352515, d354516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352515, d354516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352516 q = 0) : d354517 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d352516, d354517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352516, d354517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352517 q = 0) : d354518 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352517, d354518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352517, d354518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352518 q = 0) : d354519 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352518, d354519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352518, d354519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d352549 q = 0) : d354533 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352549, d354533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352549, d354533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro36710 (p : Pattern) (selected : d352550 p = 0) : d354534 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352514 q = 0) : d354515 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352514, d354515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36699 q selected
    | true =>
      simp only [d352514, d354515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352515 q = 0) : d354516 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352515, d354516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352515, d354516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352520 q = 0) : d354521 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d352520, d354521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352520, d354521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352521 q = 0) : d354522 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352521, d354522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352521, d354522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352522 q = 0) : d354523 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352522, d354523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352522, d354523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352550 q = 0) : d354534 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352550, d354534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352550, d354534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36711 (p : Pattern) (selected : d352553 p = 0) : d354637 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352378 q = 0) : d354511 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352378, d354511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36673 q selected
    | true =>
      simp only [d352378, d354511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352379 q = 0) : d354512 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352379, d354512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352379, d354512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352526 q = 0) : d354613 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d352526, d354613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352526, d354613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352527 q = 0) : d354614 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352527, d354614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352527, d354614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352528 q = 0) : d354615 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352528, d354615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352528, d354615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352553 q = 0) : d354637 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352553, d354637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352553, d354637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36712 (p : Pattern) (selected : d352559 p = 0) : d354643 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352415 q = 0) : d354548 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352415, d354548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36681 q selected
    | true =>
      simp only [d352415, d354548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36682 q selected
  have h2 (q : Pattern) (selected : d352416 q = 0) : d354549 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352416, d354549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352416, d354549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352417 q = 0) : d354550 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352417, d354550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352417, d354550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352418 q = 0) : d354551 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d352418, d354551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352418, d354551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352425 q = 0) : d354558 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352425, d354558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36683 q selected
    | true =>
      simp only [d352425, d354558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36684 q selected
  have h6 (q : Pattern) (selected : d352426 q = 0) : d354559 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352426, d354559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352426, d354559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d352427 q = 0) : d354560 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352427, d354560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352427, d354560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d352478 q = 0) : d354611 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352478, d354611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36693 q selected
    | true =>
      simp only [d352478, d354611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36675 q selected
  have h9 (q : Pattern) (selected : d352524 q = 0) : d354525 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352524, d354525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36700 q selected
    | true =>
      simp only [d352524, d354525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36701 q selected
  have h10 (q : Pattern) (selected : d352525 q = 0) : d354612 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352525, d354612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d352525, d354612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d352530 q = 0) : d354617 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352530, d354617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36702 q selected
    | true =>
      simp only [d352530, d354617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d352531 q = 0) : d354618 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352531, d354618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d352531, d354618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d352532 q = 0) : d354619 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352532, d354619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d352532, d354619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d352533 q = 0) : d354620 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d352533, d354620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352533, d354620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d352534 q = 0) : d354621 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d352534, d354621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352534, d354621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d352538 q = 0) : d354625 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352538, d354625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36704 q selected
    | true =>
      simp only [d352538, d354625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36705 q selected
  have h17 (q : Pattern) (selected : d352539 q = 0) : d354626 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352539, d354626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352539, d354626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d352540 q = 0) : d354627 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352540, d354627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d352540, d354627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d352541 q = 0) : d354628 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d352541, d354628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352541, d354628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d352544 q = 0) : d354631 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352544, d354631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36706 q selected
    | true =>
      simp only [d352544, d354631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36707 q selected
  have h21 (q : Pattern) (selected : d352545 q = 0) : d354632 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352545, d354632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352545, d354632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d352546 q = 0) : d354633 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352546, d354633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d352546, d354633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d352548 q = 0) : d354635 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352548, d354635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36708 q selected
    | true =>
      simp only [d352548, d354635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36678 q selected
  have h24 (q : Pattern) (selected : d352551 q = 0) : d354535 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352551, d354535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36709 q selected
    | true =>
      simp only [d352551, d354535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36710 q selected
  have h25 (q : Pattern) (selected : d352552 q = 0) : d354636 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352552, d354636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d352552, d354636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d352554 q = 0) : d354638 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352554, d354638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36711 q selected
    | true =>
      simp only [d352554, d354638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d352555 q = 0) : d354639 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352555, d354639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d352555, d354639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d352556 q = 0) : d354640 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352556, d354640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d352556, d354640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d352557 q = 0) : d354641 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d352557, d354641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d352557, d354641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d352558 q = 0) : d354642 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d352558, d354642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d352558, d354642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d352559 q = 0) : d354643 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d352559, d354643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d352559, d354643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro36713 (p : Pattern) (selected : d352566 p = 0) : d354650 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352392 q = 0) : d354525 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352392, d354525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36675 q selected
    | true =>
      simp only [d352392, d354525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36676 q selected
  have h2 (q : Pattern) (selected : d352393 q = 0) : d354526 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352393, d354526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352393, d354526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352394 q = 0) : d354527 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352394, d354527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352394, d354527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352395 q = 0) : d354528 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d352395, d354528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352395, d354528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352396 q = 0) : d354529 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d352396, d354529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352396, d354529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352561 q = 0) : d354645 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352561, d354645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36676 q selected
    | true =>
      simp only [d352561, d354645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352562 q = 0) : d354646 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352562, d354646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352562, d354646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d352563 q = 0) : d354647 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352563, d354647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352563, d354647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d352564 q = 0) : d354648 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d352564, d354648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352564, d354648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d352565 q = 0) : d354649 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d352565, d354649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352565, d354649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d352566 q = 0) : d354650 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d352566, d354650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352566, d354650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro36714 (p : Pattern) (selected : d352572 p = 0) : d354656 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352561 q = 0) : d354645 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352561, d354645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36676 q selected
    | true =>
      simp only [d352561, d354645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352562 q = 0) : d354646 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352562, d354646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352562, d354646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352563 q = 0) : d354647 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352563, d354647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352563, d354647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352564 q = 0) : d354648 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d352564, d354648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352564, d354648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352565 q = 0) : d354649 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d352565, d354649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352565, d354649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352567 q = 0) : d354651 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352567, d354651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36679 q selected
    | true =>
      simp only [d352567, d354651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352568 q = 0) : d354652 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352568, d354652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352568, d354652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d352569 q = 0) : d354653 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352569, d354653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352569, d354653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d352570 q = 0) : d354654 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d352570, d354654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352570, d354654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d352571 q = 0) : d354655 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d352571, d354655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352571, d354655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d352572 q = 0) : d354656 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d352572, d354656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352572, d354656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro36715 (p : Pattern) (selected : d352579 p = 0) : d354663 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352548 q = 0) : d354635 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352548, d354635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36708 q selected
    | true =>
      simp only [d352548, d354635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36678 q selected
  have h2 (q : Pattern) (selected : d352551 q = 0) : d354535 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352551, d354535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36709 q selected
    | true =>
      simp only [d352551, d354535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36710 q selected
  have h3 (q : Pattern) (selected : d352552 q = 0) : d354636 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352552, d354636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d352552, d354636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d352554 q = 0) : d354638 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352554, d354638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36711 q selected
    | true =>
      simp only [d352554, d354638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352555 q = 0) : d354639 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352555, d354639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352555, d354639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352556 q = 0) : d354640 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352556, d354640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352556, d354640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d352577 q = 0) : d354661 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d352577, d354661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352577, d354661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d352578 q = 0) : d354662 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d352578, d354662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352578, d354662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d352579 q = 0) : d354663 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d352579, d354663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352579, d354663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro36716 (p : Pattern) (selected : d352581 p = 0) : d354665 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352567 q = 0) : d354651 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352567, d354651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36679 q selected
    | true =>
      simp only [d352567, d354651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352568 q = 0) : d354652 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352568, d354652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352568, d354652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352569 q = 0) : d354653 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352569, d354653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352569, d354653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352570 q = 0) : d354654 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d352570, d354654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352570, d354654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352571 q = 0) : d354655 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d352571, d354655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352571, d354655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352581 q = 0) : d354665 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d352581, d354665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352581, d354665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro36717 (p : Pattern) (selected : d352601 p = 0) : d354685 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352587 q = 0) : d354671 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352587, d354671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352587, d354671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36687 q selected
  have h2 (q : Pattern) (selected : d352443 q = 0) : d354576 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352443, d354576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36687 q selected
    | true =>
      simp only [d352443, d354576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d352588 q = 0) : d354672 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352588, d354672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d352588, d354672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d352444 q = 0) : d354577 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352444, d354577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352444, d354577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352589 q = 0) : d354673 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352589, d354673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352589, d354673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352590 q = 0) : d354674 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d352590, d354674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352590, d354674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352591 q = 0) : d354675 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352591, d354675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352591, d354675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36688 q selected
  have h8 (q : Pattern) (selected : d352448 q = 0) : d354581 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352448, d354581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36688 q selected
    | true =>
      simp only [d352448, d354581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d352592 q = 0) : d354676 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352592, d354676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352592, d354676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d352449 q = 0) : d354582 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352449, d354582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d352449, d354582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d352593 q = 0) : d354677 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352593, d354677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d352593, d354677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d352594 q = 0) : d354678 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d352594, d354678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d352594, d354678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d352595 q = 0) : d354679 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d352595, d354679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352595, d354679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d352596 q = 0) : d354680 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352596, d354680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352596, d354680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36689 q selected
  have h15 (q : Pattern) (selected : d352456 q = 0) : d354589 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352456, d354589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36689 q selected
    | true =>
      simp only [d352456, d354589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d352597 q = 0) : d354681 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352597, d354681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d352597, d354681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d352457 q = 0) : d354590 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352457, d354590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d352457, d354590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d352598 q = 0) : d354682 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352598, d354682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d352598, d354682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d352599 q = 0) : d354683 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d352599, d354683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d352599, d354683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d352307 q = 0) : d354459 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352307, d354459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352307, d354459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36642 q selected
  have h21 (q : Pattern) (selected : d352207 q = 0) : d354389 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352207, d354389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36642 q selected
    | true =>
      simp only [d352207, d354389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d352308 q = 0) : d354460 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352308, d354460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d352308, d354460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d352208 q = 0) : d354390 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352208, d354390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d352208, d354390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d352309 q = 0) : d354461 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352309, d354461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d352309, d354461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d352310 q = 0) : d354462 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d352310, d354462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d352310, d354462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d352600 q = 0) : d354684 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d352600, d354684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d352600, d354684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d352601 q = 0) : d354685 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d352601, d354685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d352601, d354685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro36718 (p : Pattern) (selected : d352605 p = 0) : d354689 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352307 q = 0) : d354459 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352307, d354459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352307, d354459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36642 q selected
  have h2 (q : Pattern) (selected : d352207 q = 0) : d354389 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352207, d354389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36642 q selected
    | true =>
      simp only [d352207, d354389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d352308 q = 0) : d354460 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352308, d354460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d352308, d354460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d352208 q = 0) : d354390 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352208, d354390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352208, d354390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352309 q = 0) : d354461 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352309, d354461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352309, d354461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352310 q = 0) : d354462 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d352310, d354462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352310, d354462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d351951 q = 0) : d354183 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d351951, d354183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d351951, d354183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36592 q selected
  have h8 (q : Pattern) (selected : d351910 q = 0) : d354142 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d351910, d354142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36592 q selected
    | true =>
      simp only [d351910, d354142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d351952 q = 0) : d354184 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d351952, d354184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d351952, d354184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d351911 q = 0) : d354143 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d351911, d354143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d351911, d354143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d351953 q = 0) : d354185 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d351953, d354185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d351953, d354185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d351954 q = 0) : d354186 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d351954, d354186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d351954, d354186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d352311 q = 0) : d354463 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d352311, d354463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352311, d354463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d351955 q = 0) : d354187 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d351955, d354187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d351955, d354187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d352605 q = 0) : d354689 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d352605, d354689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d352605, d354689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro36719 (p : Pattern) (selected : d352611 p = 0) : d354695 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352602 q = 0) : d354686 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d352602, d354686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36717 q selected
    | true =>
      simp only [d352602, d354686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36662 q selected
  have h2 (q : Pattern) (selected : d352603 q = 0) : d354687 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d352603, d354687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352603, d354687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352604 q = 0) : d354688 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d352604, d354688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352604, d354688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d352606 q = 0) : d354690 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d352606, d354690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36662 q selected
    | true =>
      simp only [d352606, d354690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36718 q selected
  have h5 (q : Pattern) (selected : d352607 q = 0) : d354691 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d352607, d354691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352607, d354691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352608 q = 0) : d354692 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d352608, d354692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352608, d354692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d352609 q = 0) : d354693 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d352609, d354693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352609, d354693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d352313 q = 0) : d354465 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d352313, d354465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36662 q selected
    | true =>
      simp only [d352313, d354465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36627 q selected
  have h9 (q : Pattern) (selected : d352314 q = 0) : d354466 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d352314, d354466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352314, d354466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d352315 q = 0) : d354467 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d352315, d354467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352315, d354467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d352113 q = 0) : d354314 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d352113, d354314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36627 q selected
    | true =>
      simp only [d352113, d354314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36600 q selected
  have h12 (q : Pattern) (selected : d352114 q = 0) : d354315 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d352114, d354315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352114, d354315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d352115 q = 0) : d354316 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d352115, d354316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352115, d354316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d352316 q = 0) : d354468 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d352316, d354468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d352316, d354468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d352610 q = 0) : d354694 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d352610, d354694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352610, d354694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d352611 q = 0) : d354695 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d352611, d354695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d352611, d354695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro36720 (p : Pattern) (selected : d352616 p = 0) : d354700 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352313 q = 0) : d354465 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d352313, d354465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36662 q selected
    | true =>
      simp only [d352313, d354465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36627 q selected
  have h2 (q : Pattern) (selected : d352314 q = 0) : d354466 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d352314, d354466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352314, d354466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352315 q = 0) : d354467 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d352315, d354467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352315, d354467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d352113 q = 0) : d354314 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d352113, d354314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36627 q selected
    | true =>
      simp only [d352113, d354314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36600 q selected
  have h5 (q : Pattern) (selected : d352114 q = 0) : d354315 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d352114, d354315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352114, d354315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352115 q = 0) : d354316 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d352115, d354316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352115, d354316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d352316 q = 0) : d354468 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d352316, d354468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352316, d354468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d352614 q = 0) : d354698 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d352614, d354698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352614, d354698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d352615 q = 0) : d354699 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d352615, d354699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352615, d354699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d352616 q = 0) : d354700 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d352616, d354700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d352616, d354700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro36721 (p : Pattern) (selected : d352622 p = 0) : d354706 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352612 q = 0) : d354696 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352612, d354696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36719 q selected
    | true =>
      simp only [d352612, d354696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352613 q = 0) : d354697 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352613, d354697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352613, d354697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352617 q = 0) : d354701 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352617, d354701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36720 q selected
    | true =>
      simp only [d352617, d354701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352618 q = 0) : d354702 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352618, d354702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352618, d354702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352619 q = 0) : d354703 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d352619, d354703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352619, d354703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352620 q = 0) : d354704 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352620, d354704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352620, d354704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352621 q = 0) : d354705 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352621, d354705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352621, d354705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d352622 q = 0) : d354706 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352622, d354706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352622, d354706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro36722 (p : Pattern) (selected : d352624 p = 0) : d354708 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352113 q = 0) : d354314 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d352113, d354314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36627 q selected
    | true =>
      simp only [d352113, d354314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36600 q selected
  have h2 (q : Pattern) (selected : d352114 q = 0) : d354315 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d352114, d354315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352114, d354315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352115 q = 0) : d354316 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d352115, d354316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352115, d354316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d352614 q = 0) : d354698 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d352614, d354698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352614, d354698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352623 q = 0) : d354707 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d352623, d354707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352623, d354707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352624 q = 0) : d354708 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d352624, d354708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352624, d354708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36723 (p : Pattern) (selected : d352630 p = 0) : d354714 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352617 q = 0) : d354701 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352617, d354701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36720 q selected
    | true =>
      simp only [d352617, d354701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352618 q = 0) : d354702 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352618, d354702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352618, d354702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352625 q = 0) : d354709 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352625, d354709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36722 q selected
    | true =>
      simp only [d352625, d354709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352626 q = 0) : d354710 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352626, d354710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352626, d354710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352627 q = 0) : d354711 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d352627, d354711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352627, d354711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352628 q = 0) : d354712 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352628, d354712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352628, d354712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352629 q = 0) : d354713 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352629, d354713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352629, d354713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d352630 q = 0) : d354714 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352630, d354714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352630, d354714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro36724 (p : Pattern) (selected : d352642 p = 0) : d354464 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352632 q = 0) : d354454 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352632, d354454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352632, d354454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36695 q selected
  have h2 (q : Pattern) (selected : d352489 q = 0) : d354381 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352489, d354381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36695 q selected
    | true =>
      simp only [d352489, d354381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d352633 q = 0) : d354455 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352633, d354455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d352633, d354455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d352490 q = 0) : d354382 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352490, d354382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352490, d354382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352634 q = 0) : d354456 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352634, d354456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352634, d354456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352635 q = 0) : d354457 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d352635, d354457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352635, d354457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352326 q = 0) : d354308 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352326, d354308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352326, d354308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36647 q selected
  have h8 (q : Pattern) (selected : d352235 q = 0) : d354254 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352235, d354254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36647 q selected
    | true =>
      simp only [d352235, d354254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d352327 q = 0) : d354309 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352327, d354309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352327, d354309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d352236 q = 0) : d354255 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352236, d354255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d352236, d354255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d352328 q = 0) : d354310 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352328, d354310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d352328, d354310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d352329 q = 0) : d354311 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d352329, d354311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d352329, d354311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d352636 q = 0) : d354458 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d352636, d354458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352636, d354458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d352637 q = 0) : d354459 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352637, d354459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352637, d354459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36696 q selected
  have h15 (q : Pattern) (selected : d352497 q = 0) : d354389 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352497, d354389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36696 q selected
    | true =>
      simp only [d352497, d354389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d352638 q = 0) : d354460 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352638, d354460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d352638, d354460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d352498 q = 0) : d354390 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352498, d354390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d352498, d354390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d352639 q = 0) : d354461 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352639, d354461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d352639, d354461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d352640 q = 0) : d354462 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d352640, d354462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d352640, d354462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d352126 q = 0) : d354183 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352126, d354183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352126, d354183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36615 q selected
  have h21 (q : Pattern) (selected : d352051 q = 0) : d354142 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352051, d354142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36615 q selected
    | true =>
      simp only [d352051, d354142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d352127 q = 0) : d354184 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352127, d354184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d352127, d354184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d352052 q = 0) : d354143 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352052, d354143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d352052, d354143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d352128 q = 0) : d354185 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352128, d354185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d352128, d354185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d352129 q = 0) : d354186 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d352129, d354186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d352129, d354186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d352641 q = 0) : d354463 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d352641, d354463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d352641, d354463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d352642 q = 0) : d354464 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d352642, d354464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d352642, d354464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro36725 (p : Pattern) (selected : d352649 p = 0) : d354700 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352643 q = 0) : d354465 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d352643, d354465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36724 q selected
    | true =>
      simp only [d352643, d354465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36665 q selected
  have h2 (q : Pattern) (selected : d352644 q = 0) : d354466 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d352644, d354466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352644, d354466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352645 q = 0) : d354467 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d352645, d354467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352645, d354467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d352332 q = 0) : d354314 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d352332, d354314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36665 q selected
    | true =>
      simp only [d352332, d354314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36630 q selected
  have h5 (q : Pattern) (selected : d352333 q = 0) : d354315 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d352333, d354315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352333, d354315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352334 q = 0) : d354316 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d352334, d354316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352334, d354316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d352646 q = 0) : d354468 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d352646, d354468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352646, d354468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d352647 q = 0) : d354698 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d352647, d354698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352647, d354698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d352648 q = 0) : d354699 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d352648, d354699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352648, d354699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d352649 q = 0) : d354700 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d352649, d354700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d352649, d354700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro36726 (p : Pattern) (selected : d352653 p = 0) : d354708 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352332 q = 0) : d354314 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d352332, d354314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36665 q selected
    | true =>
      simp only [d352332, d354314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36630 q selected
  have h2 (q : Pattern) (selected : d352333 q = 0) : d354315 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d352333, d354315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352333, d354315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352334 q = 0) : d354316 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d352334, d354316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352334, d354316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d352647 q = 0) : d354698 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d352647, d354698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352647, d354698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352652 q = 0) : d354707 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d352652, d354707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352652, d354707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352653 q = 0) : d354708 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d352653, d354708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352653, d354708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36727 (p : Pattern) (selected : d352659 p = 0) : d354714 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352650 q = 0) : d354701 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352650, d354701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36725 q selected
    | true =>
      simp only [d352650, d354701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352651 q = 0) : d354702 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352651, d354702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352651, d354702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352654 q = 0) : d354709 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352654, d354709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36726 q selected
    | true =>
      simp only [d352654, d354709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352655 q = 0) : d354710 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352655, d354710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352655, d354710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352656 q = 0) : d354711 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d352656, d354711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352656, d354711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352657 q = 0) : d354712 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352657, d354712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352657, d354712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352658 q = 0) : d354713 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352658, d354713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352658, d354713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d352659 q = 0) : d354714 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352659, d354714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352659, d354714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro36728 (p : Pattern) (selected : d352663 p = 0) : d354719 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352654 q = 0) : d354709 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352654, d354709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36726 q selected
    | true =>
      simp only [d352654, d354709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352655 q = 0) : d354710 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352655, d354710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352655, d354710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352660 q = 0) : d354716 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d352660, d354716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352660, d354716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352661 q = 0) : d354717 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352661, d354717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352661, d354717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352662 q = 0) : d354718 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352662, d354718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352662, d354718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352663 q = 0) : d354719 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352663, d354719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352663, d354719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36729 (p : Pattern) (selected : d352669 p = 0) : d354725 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352617 q = 0) : d354701 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352617, d354701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36720 q selected
    | true =>
      simp only [d352617, d354701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352618 q = 0) : d354702 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352618, d354702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352618, d354702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352666 q = 0) : d354722 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d352666, d354722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352666, d354722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352667 q = 0) : d354723 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352667, d354723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352667, d354723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352668 q = 0) : d354724 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352668, d354724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352668, d354724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352669 q = 0) : d354725 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352669, d354725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352669, d354725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36730 (p : Pattern) (selected : d352675 p = 0) : d354731 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352631 q = 0) : d354715 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352631, d354715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36721 q selected
    | true =>
      simp only [d352631, d354715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36723 q selected
  have h2 (q : Pattern) (selected : d352664 q = 0) : d354720 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352664, d354720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36727 q selected
    | true =>
      simp only [d352664, d354720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36728 q selected
  have h3 (q : Pattern) (selected : d352665 q = 0) : d354721 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352665, d354721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d352665, d354721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d352670 q = 0) : d354726 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352670, d354726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36729 q selected
    | true =>
      simp only [d352670, d354726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352671 q = 0) : d354727 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352671, d354727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352671, d354727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352672 q = 0) : d354728 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352672, d354728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352672, d354728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d352673 q = 0) : d354729 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d352673, d354729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352673, d354729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d352674 q = 0) : d354730 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d352674, d354730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352674, d354730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d352675 q = 0) : d354731 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d352675, d354731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352675, d354731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro36731 (p : Pattern) (selected : d352680 p = 0) : d354719 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352625 q = 0) : d354709 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352625, d354709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36722 q selected
    | true =>
      simp only [d352625, d354709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352626 q = 0) : d354710 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352626, d354710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352626, d354710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352677 q = 0) : d354716 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d352677, d354716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352677, d354716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352678 q = 0) : d354717 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352678, d354717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352678, d354717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352679 q = 0) : d354718 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352679, d354718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352679, d354718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352680 q = 0) : d354719 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352680, d354719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352680, d354719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36732 (p : Pattern) (selected : d352686 p = 0) : d354738 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352681 q = 0) : d354733 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352681, d354733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36731 q selected
    | true =>
      simp only [d352681, d354733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352682 q = 0) : d354734 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352682, d354734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352682, d354734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352683 q = 0) : d354735 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352683, d354735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352683, d354735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352684 q = 0) : d354736 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d352684, d354736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352684, d354736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352685 q = 0) : d354737 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d352685, d354737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352685, d354737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352686 q = 0) : d354738 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d352686, d354738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352686, d354738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro36733 (p : Pattern) (selected : d352692 p = 0) : d354744 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352398 q = 0) : d354531 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d352398, d354531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352398, d354531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36677 q selected
  have h2 (q : Pattern) (selected : d352399 q = 0) : d354532 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d352399, d354532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d352399, d354532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d352408 q = 0) : d354541 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d352408, d354541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36677 q selected
    | true =>
      simp only [d352408, d354541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36680 q selected
  have h4 (q : Pattern) (selected : d352409 q = 0) : d354542 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d352409, d354542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352409, d354542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352410 q = 0) : d354543 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d352410, d354543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352410, d354543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352560 q = 0) : d354644 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d352560, d354644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36703 q selected
    | true =>
      simp only [d352560, d354644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36712 q selected
  have h7 (q : Pattern) (selected : d352573 q = 0) : d354657 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d352573, d354657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36713 q selected
    | true =>
      simp only [d352573, d354657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36714 q selected
  have h8 (q : Pattern) (selected : d352574 q = 0) : d354658 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d352574, d354658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352574, d354658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d352575 q = 0) : d354659 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d352575, d354659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d352575, d354659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d352576 q = 0) : d354660 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d352576, d354660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352576, d354660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d352580 q = 0) : d354664 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d352580, d354664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352580, d354664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36715 q selected
  have h12 (q : Pattern) (selected : d352582 q = 0) : d354666 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d352582, d354666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352582, d354666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36716 q selected
  have h13 (q : Pattern) (selected : d352583 q = 0) : d354667 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d352583, d354667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d352583, d354667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d352584 q = 0) : d354668 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d352584, d354668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d352584, d354668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d352585 q = 0) : d354669 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d352585, d354669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d352585, d354669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d352586 q = 0) : d354670 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d352586, d354670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d352586, d354670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d352676 q = 0) : d354732 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d352676, d354732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352676, d354732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36730 q selected
  have h18 (q : Pattern) (selected : d352687 q = 0) : d354739 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d352687, d354739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352687, d354739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36732 q selected
  have h19 (q : Pattern) (selected : d352688 q = 0) : d354740 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d352688, d354740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d352688, d354740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d352689 q = 0) : d354741 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d352689, d354741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d352689, d354741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d352690 q = 0) : d354742 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d352690, d354742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d352690, d354742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d352691 q = 0) : d354743 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d352691, d354743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d352691, d354743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d352692 q = 0) : d354744 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d352692, d354744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d352692, d354744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro36734 (p : Pattern) (selected : d352698 p = 0) : d354750 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352693 q = 0) : d354745 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d352693, d354745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352693, d354745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36733 q selected
  have h2 (q : Pattern) (selected : d352694 q = 0) : d354746 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d352694, d354746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352694, d354746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352695 q = 0) : d354747 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d352695, d354747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352695, d354747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d352696 q = 0) : d354748 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d352696, d354748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352696, d354748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352697 q = 0) : d354749 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d352697, d354749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352697, d354749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352698 q = 0) : d354750 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d352698, d354750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352698, d354750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro36735 (p : Pattern) (selected : d352701 p = 0) : d354753 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352016 q = 0) : d354248 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d352016, d354248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36609 q selected
    | true =>
      simp only [d352016, d354248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352017 q = 0) : d354249 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d352017, d354249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d352017, d354249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d351904 q = 0) : d354136 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d351904, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36591 q selected
    | true =>
      simp only [d351904, d354136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d351905 q = 0) : d354137 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d351905, d354137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d351905, d354137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352018 q = 0) : d354250 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d352018, d354250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352018, d354250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d351906 q = 0) : d354138 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d351906, d354138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d351906, d354138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352019 q = 0) : d354251 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d352019, d354251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352019, d354251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d352020 q = 0) : d354252 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d352020, d354252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352020, d354252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d352701 q = 0) : d354753 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d352701, d354753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d352701, d354753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro36736 (p : Pattern) (selected : d352707 p = 0) : d354759 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352443 q = 0) : d354576 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352443, d354576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36687 q selected
    | true =>
      simp only [d352443, d354576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352444 q = 0) : d354577 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352444, d354577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d352444, d354577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d352445 q = 0) : d354578 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352445, d354578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352445, d354578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d352446 q = 0) : d354579 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d352446, d354579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352446, d354579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352448 q = 0) : d354581 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352448, d354581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36688 q selected
    | true =>
      simp only [d352448, d354581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352449 q = 0) : d354582 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352449, d354582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352449, d354582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352450 q = 0) : d354583 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352450, d354583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352450, d354583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d352451 q = 0) : d354584 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d352451, d354584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352451, d354584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d352452 q = 0) : d354585 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d352452, d354585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352452, d354585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d352456 q = 0) : d354589 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352456, d354589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36689 q selected
    | true =>
      simp only [d352456, d354589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d352457 q = 0) : d354590 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352457, d354590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d352457, d354590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d352458 q = 0) : d354591 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352458, d354591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352458, d354591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d352459 q = 0) : d354592 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d352459, d354592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d352459, d354592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d352702 q = 0) : d354754 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352702, d354754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36735 q selected
    | true =>
      simp only [d352702, d354754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d352703 q = 0) : d354755 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352703, d354755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d352703, d354755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d352704 q = 0) : d354756 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352704, d354756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352704, d354756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d352705 q = 0) : d354757 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d352705, d354757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d352705, d354757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d352706 q = 0) : d354758 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d352706, d354758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d352706, d354758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d352707 q = 0) : d354759 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d352707, d354759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d352707, d354759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro36737 (p : Pattern) (selected : d352710 p = 0) : d354762 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352199 q = 0) : d354381 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352199, d354381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36641 q selected
    | true =>
      simp only [d352199, d354381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352200 q = 0) : d354382 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352200, d354382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d352200, d354382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d352201 q = 0) : d354383 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352201, d354383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352201, d354383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d352202 q = 0) : d354384 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d352202, d354384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352202, d354384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352702 q = 0) : d354754 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352702, d354754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36735 q selected
    | true =>
      simp only [d352702, d354754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352703 q = 0) : d354755 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352703, d354755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352703, d354755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352704 q = 0) : d354756 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352704, d354756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352704, d354756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d352705 q = 0) : d354757 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d352705, d354757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352705, d354757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d352708 q = 0) : d354760 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d352708, d354760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352708, d354760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d352709 q = 0) : d354761 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d352709, d354761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d352709, d354761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d352710 q = 0) : d354762 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d352710, d354762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d352710, d354762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro36738 (p : Pattern) (selected : d352714 p = 0) : d354766 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352702 q = 0) : d354754 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d352702, d354754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36735 q selected
    | true =>
      simp only [d352702, d354754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352703 q = 0) : d354755 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d352703, d354755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d352703, d354755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d352704 q = 0) : d354756 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352704, d354756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352704, d354756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d352705 q = 0) : d354757 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d352705, d354757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352705, d354757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352709 q = 0) : d354761 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d352709, d354761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352709, d354761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352714 q = 0) : d354766 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d352714, d354766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352714, d354766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36739 (p : Pattern) (selected : d352721 p = 0) : d354773 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352711 q = 0) : d354763 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d352711, d354763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36736 q selected
    | true =>
      simp only [d352711, d354763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36737 q selected
  have h2 (q : Pattern) (selected : d352712 q = 0) : d354764 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d352712, d354764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352712, d354764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352713 q = 0) : d354765 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d352713, d354765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352713, d354765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d352715 q = 0) : d354767 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d352715, d354767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36737 q selected
    | true =>
      simp only [d352715, d354767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36738 q selected
  have h5 (q : Pattern) (selected : d352716 q = 0) : d354768 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d352716, d354768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352716, d354768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352717 q = 0) : d354769 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d352717, d354769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352717, d354769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d352718 q = 0) : d354770 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d352718, d354770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352718, d354770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d352719 q = 0) : d354771 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d352719, d354771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352719, d354771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d352720 q = 0) : d354772 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d352720, d354772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352720, d354772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d352721 q = 0) : d354773 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d352721, d354773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d352721, d354773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro36740 (p : Pattern) (selected : d352725 p = 0) : d354777 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352715 q = 0) : d354767 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d352715, d354767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36737 q selected
    | true =>
      simp only [d352715, d354767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36738 q selected
  have h2 (q : Pattern) (selected : d352716 q = 0) : d354768 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d352716, d354768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352716, d354768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352717 q = 0) : d354769 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d352717, d354769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352717, d354769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d352719 q = 0) : d354771 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d352719, d354771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352719, d354771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352724 q = 0) : d354776 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d352724, d354776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352724, d354776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352725 q = 0) : d354777 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d352725, d354777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352725, d354777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36741 (p : Pattern) (selected : d352731 p = 0) : d354783 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352722 q = 0) : d354774 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352722, d354774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36739 q selected
    | true =>
      simp only [d352722, d354774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352723 q = 0) : d354775 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352723, d354775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352723, d354775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352726 q = 0) : d354778 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352726, d354778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36740 q selected
    | true =>
      simp only [d352726, d354778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352727 q = 0) : d354779 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352727, d354779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352727, d354779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352728 q = 0) : d354780 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d352728, d354780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352728, d354780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352729 q = 0) : d354781 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352729, d354781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352729, d354781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352730 q = 0) : d354782 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352730, d354782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352730, d354782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d352731 q = 0) : d354783 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352731, d354783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352731, d354783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro36742 (p : Pattern) (selected : d352735 p = 0) : d354787 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352726 q = 0) : d354778 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352726, d354778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36740 q selected
    | true =>
      simp only [d352726, d354778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352727 q = 0) : d354779 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352727, d354779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352727, d354779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352732 q = 0) : d354784 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d352732, d354784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352732, d354784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352733 q = 0) : d354785 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352733, d354785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352733, d354785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352734 q = 0) : d354786 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352734, d354786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352734, d354786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352735 q = 0) : d354787 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352735, d354787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352735, d354787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro36743 (p : Pattern) (selected : d352741 p = 0) : d354793 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352736 q = 0) : d354788 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352736, d354788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36741 q selected
    | true =>
      simp only [d352736, d354788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36742 q selected
  have h2 (q : Pattern) (selected : d352737 q = 0) : d354789 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352737, d354789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352737, d354789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352738 q = 0) : d354790 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352738, d354790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352738, d354790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352739 q = 0) : d354791 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d352739, d354791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352739, d354791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352740 q = 0) : d354792 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d352740, d354792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352740, d354792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352741 q = 0) : d354793 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d352741, d354793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352741, d354793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro36744 (p : Pattern) (selected : d352744 p = 0) : d354796 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352722 q = 0) : d354774 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352722, d354774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36739 q selected
    | true =>
      simp only [d352722, d354774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352723 q = 0) : d354775 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352723, d354775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352723, d354775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352726 q = 0) : d354778 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352726, d354778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36740 q selected
    | true =>
      simp only [d352726, d354778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352727 q = 0) : d354779 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352727, d354779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352727, d354779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352728 q = 0) : d354780 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d352728, d354780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352728, d354780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352729 q = 0) : d354781 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352729, d354781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352729, d354781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352730 q = 0) : d354782 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352730, d354782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352730, d354782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d352744 q = 0) : d354796 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352744, d354796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352744, d354796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro36745 (p : Pattern) (selected : d352745 p = 0) : d354797 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352726 q = 0) : d354778 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352726, d354778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36740 q selected
    | true =>
      simp only [d352726, d354778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352727 q = 0) : d354779 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352727, d354779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352727, d354779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352732 q = 0) : d354784 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d352732, d354784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352732, d354784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352733 q = 0) : d354785 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352733, d354785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352733, d354785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352734 q = 0) : d354786 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352734, d354786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d352734, d354786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d352745 q = 0) : d354797 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352745, d354797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352745, d354797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro36746 (p : Pattern) (selected : d352751 p = 0) : d354803 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352736 q = 0) : d354788 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352736, d354788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36741 q selected
    | true =>
      simp only [d352736, d354788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36742 q selected
  have h2 (q : Pattern) (selected : d352737 q = 0) : d354789 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352737, d354789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352737, d354789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352738 q = 0) : d354790 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352738, d354790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352738, d354790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352739 q = 0) : d354791 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d352739, d354791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352739, d354791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352740 q = 0) : d354792 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d352740, d354792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352740, d354792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352746 q = 0) : d354798 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d352746, d354798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36744 q selected
    | true =>
      simp only [d352746, d354798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36745 q selected
  have h7 (q : Pattern) (selected : d352747 q = 0) : d354799 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d352747, d354799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352747, d354799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d352748 q = 0) : d354800 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d352748, d354800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d352748, d354800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d352749 q = 0) : d354801 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d352749, d354801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352749, d354801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d352750 q = 0) : d354802 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d352750, d354802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352750, d354802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d352751 q = 0) : d354803 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d352751, d354803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352751, d354803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro36747 (p : Pattern) (selected : d352756 p = 0) : d354808 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352722 q = 0) : d354774 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352722, d354774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36739 q selected
    | true =>
      simp only [d352722, d354774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352723 q = 0) : d354775 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352723, d354775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352723, d354775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352726 q = 0) : d354778 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352726, d354778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36740 q selected
    | true =>
      simp only [d352726, d354778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352727 q = 0) : d354779 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352727, d354779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352727, d354779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352728 q = 0) : d354780 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d352728, d354780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352728, d354780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352729 q = 0) : d354781 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352729, d354781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d352729, d354781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d352755 q = 0) : d354807 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352755, d354807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352755, d354807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d352756 q = 0) : d354808 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352756, d354808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352756, d354808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro36748 (p : Pattern) (selected : d352758 p = 0) : d354810 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352726 q = 0) : d354778 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352726, d354778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36740 q selected
    | true =>
      simp only [d352726, d354778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352727 q = 0) : d354779 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352727, d354779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352727, d354779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352732 q = 0) : d354784 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d352732, d354784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352732, d354784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352733 q = 0) : d354785 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352733, d354785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d352733, d354785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d352757 q = 0) : d354809 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352757, d354809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352757, d354809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352758 q = 0) : d354810 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352758, d354810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352758, d354810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro36749 (p : Pattern) (selected : d352765 p = 0) : d354817 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d352722 q = 0) : d354774 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352722, d354774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36739 q selected
    | true =>
      simp only [d352722, d354774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d352723 q = 0) : d354775 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352723, d354775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352723, d354775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d352726 q = 0) : d354778 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d352726, d354778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36740 q selected
    | true =>
      simp only [d352726, d354778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d352727 q = 0) : d354779 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d352727, d354779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352727, d354779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d352728 q = 0) : d354780 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d352728, d354780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d352728, d354780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d352763 q = 0) : d354815 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d352763, d354815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352763, d354815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d352764 q = 0) : d354816 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d352764, d354816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d352764, d354816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d352765 q = 0) : d354817 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d352765, d354817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352765, d354817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
end NetHack.Soko22Hazard87
