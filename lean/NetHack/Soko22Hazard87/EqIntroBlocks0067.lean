import NetHack.Soko22Hazard87.EqIntroBlocks0066
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro16750 (p : Pattern) (selected : d182425 p = 1) : d184556 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182420 q = 1) : d184551 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d182420, d184551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182420, d184551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16749 q selected
  have h2 (q : Pattern) (selected : d182421 q = 1) : d184552 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d182421, d184552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182421, d184552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182422 q = 1) : d184553 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d182422, d184553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182422, d184553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182423 q = 1) : d184554 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d182423, d184554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182423, d184554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d182424 q = 1) : d184555 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d182424, d184555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182424, d184555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182425 q = 1) : d184556 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d182425, d184556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182425, d184556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16751 (p : Pattern) (selected : d182521 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182511 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro113 q selected
    | true =>
      simp only [d182511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182512 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182513 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6855 q selected
    | true =>
      simp only [d182513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182514 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182515 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182516 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6856 q selected
    | true =>
      simp only [d182516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182517 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d182518 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6857 q selected
    | true =>
      simp only [d182518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d182519 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d182519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d182520 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d182521 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16752 (p : Pattern) (selected : d182528 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182522 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro116 q selected
    | true =>
      simp only [d182522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182523 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182524 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6859 q selected
    | true =>
      simp only [d182524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182525 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182526 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182518 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6857 q selected
    | true =>
      simp only [d182518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182519 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d182527 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d182528 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro16753 (p : Pattern) (selected : d182538 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182532 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6861 q selected
    | true =>
      simp only [d182532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182533 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182534 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182535 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6862 q selected
    | true =>
      simp only [d182535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182536 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182537 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182538 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16754 (p : Pattern) (selected : d182546 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182543 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro117 q selected
    | true =>
      simp only [d182543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182544 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182545 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182535 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6862 q selected
    | true =>
      simp only [d182535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182536 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182537 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182546 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16755 (p : Pattern) (selected : d182552 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182529 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16751 q selected
    | true =>
      simp only [d182529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16752 q selected
  have h2 (q : Pattern) (selected : d182530 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182531 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182539 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16752 q selected
    | true =>
      simp only [d182539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16753 q selected
  have h5 (q : Pattern) (selected : d182540 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182541 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d182542 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d182547 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16752 q selected
    | true =>
      simp only [d182547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16754 q selected
  have h9 (q : Pattern) (selected : d182548 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d182549 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d182550 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d182550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d182551 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d182551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d182552 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d182552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d182552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro16756 (p : Pattern) (selected : d182556 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182547 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16752 q selected
    | true =>
      simp only [d182547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16754 q selected
  have h2 (q : Pattern) (selected : d182548 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182549 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182550 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182555 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d182555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182556 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d182556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16757 (p : Pattern) (selected : d182562 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182553 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16755 q selected
    | true =>
      simp only [d182553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182554 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182557 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16756 q selected
    | true =>
      simp only [d182557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182558 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d182559 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d182559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182560 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d182560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182561 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d182561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d182562 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d182562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16758 (p : Pattern) (selected : d182566 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182557 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16756 q selected
    | true =>
      simp only [d182557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182558 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182563 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d182563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182564 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d182564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182565 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d182565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182566 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d182566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16759 (p : Pattern) (selected : d182587 p = 1) : d184564 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182510 q = 1) : d182510 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d182567 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d182567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16757 q selected
    | true =>
      simp only [d182567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16758 q selected
  have h3 (q : Pattern) (selected : d182568 q = 1) : d184560 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d182568, d184560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182568, d184560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182583 q = 1) : d182583 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d182584 q = 1) : d184561 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d182584, d184561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182584, d184561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182585 q = 1) : d184562 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d182585, d184562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182585, d184562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d182586 q = 1) : d184563 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d182586, d184563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182586, d184563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d182587 q = 1) : d184564 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d182587, d184564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182587, d184564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16760 (p : Pattern) (selected : d182604 p = 1) : d184570 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182588 q = 1) : d184565 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d182588, d184565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182588, d184565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16759 q selected
  have h2 (q : Pattern) (selected : d182599 q = 1) : d182599 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d182600 q = 1) : d184566 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d182600, d184566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182600, d184566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182601 q = 1) : d184567 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d182601, d184567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182601, d184567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182602 q = 1) : d184568 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d182602, d184568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182602, d184568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182603 q = 1) : d184569 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d182603, d184569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182603, d184569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182604 q = 1) : d184570 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d182604, d184570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182604, d184570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16761 (p : Pattern) (selected : d182610 p = 1) : d184576 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182605 q = 1) : d184571 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d182605, d184571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182605, d184571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16760 q selected
  have h2 (q : Pattern) (selected : d182606 q = 1) : d184572 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d182606, d184572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182606, d184572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182607 q = 1) : d184573 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d182607, d184573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182607, d184573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182608 q = 1) : d184574 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d182608, d184574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182608, d184574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d182609 q = 1) : d184575 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d182609, d184575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182609, d184575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182610 q = 1) : d184576 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d182610, d184576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182610, d184576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16762 (p : Pattern) (selected : d182702 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182692 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro148 q selected
    | true =>
      simp only [d182692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182693 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182694 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6872 q selected
    | true =>
      simp only [d182694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182695 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182696 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182697 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6873 q selected
    | true =>
      simp only [d182697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182698 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d182699 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6874 q selected
    | true =>
      simp only [d182699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d182700 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d182700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d182701 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d182702 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16763 (p : Pattern) (selected : d182709 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182703 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro153 q selected
    | true =>
      simp only [d182703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182704 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182705 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6876 q selected
    | true =>
      simp only [d182705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182706 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182707 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182699 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6874 q selected
    | true =>
      simp only [d182699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182700 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d182708 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d182709 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro16764 (p : Pattern) (selected : d182719 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182713 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6878 q selected
    | true =>
      simp only [d182713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182714 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182715 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182716 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6879 q selected
    | true =>
      simp only [d182716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182717 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182718 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182719 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16765 (p : Pattern) (selected : d182727 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182724 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro154 q selected
    | true =>
      simp only [d182724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182725 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182726 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182716 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6879 q selected
    | true =>
      simp only [d182716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182717 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182718 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182727 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16766 (p : Pattern) (selected : d182733 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182710 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16762 q selected
    | true =>
      simp only [d182710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16763 q selected
  have h2 (q : Pattern) (selected : d182711 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182712 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182720 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16763 q selected
    | true =>
      simp only [d182720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16764 q selected
  have h5 (q : Pattern) (selected : d182721 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182722 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d182723 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d182728 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16763 q selected
    | true =>
      simp only [d182728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16765 q selected
  have h9 (q : Pattern) (selected : d182729 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d182730 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d182731 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d182731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d182732 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d182732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d182733 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d182733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d182733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro16767 (p : Pattern) (selected : d182737 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182728 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16763 q selected
    | true =>
      simp only [d182728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16765 q selected
  have h2 (q : Pattern) (selected : d182729 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182730 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182731 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182736 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d182736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182737 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d182737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16768 (p : Pattern) (selected : d182743 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16766 q selected
    | true =>
      simp only [d182734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182738 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16767 q selected
    | true =>
      simp only [d182738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182739 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d182740 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d182740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182741 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d182741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182742 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d182742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d182743 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d182743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16769 (p : Pattern) (selected : d182747 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182738 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16767 q selected
    | true =>
      simp only [d182738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182739 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182744 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d182744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182745 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d182745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182746 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d182746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182747 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d182747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16770 (p : Pattern) (selected : d182768 p = 1) : d184585 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182691 q = 1) : d182691 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d182748 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d182748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16768 q selected
    | true =>
      simp only [d182748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16769 q selected
  have h3 (q : Pattern) (selected : d182749 q = 1) : d184581 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d182749, d184581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182749, d184581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182764 q = 1) : d182764 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d182765 q = 1) : d184582 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d182765, d184582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182765, d184582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182766 q = 1) : d184583 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d182766, d184583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182766, d184583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d182767 q = 1) : d184584 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d182767, d184584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182767, d184584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d182768 q = 1) : d184585 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d182768, d184585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182768, d184585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16771 (p : Pattern) (selected : d182785 p = 1) : d184591 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182769 q = 1) : d184586 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d182769, d184586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182769, d184586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16770 q selected
  have h2 (q : Pattern) (selected : d182780 q = 1) : d182780 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d182781 q = 1) : d184587 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d182781, d184587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182781, d184587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182782 q = 1) : d184588 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d182782, d184588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182782, d184588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182783 q = 1) : d184589 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d182783, d184589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182783, d184589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182784 q = 1) : d184590 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d182784, d184590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182784, d184590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182785 q = 1) : d184591 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d182785, d184591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182785, d184591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16772 (p : Pattern) (selected : d182791 p = 1) : d184597 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182786 q = 1) : d184592 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d182786, d184592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182786, d184592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16771 q selected
  have h2 (q : Pattern) (selected : d182787 q = 1) : d184593 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d182787, d184593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182787, d184593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182788 q = 1) : d184594 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d182788, d184594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182788, d184594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182789 q = 1) : d184595 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d182789, d184595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182789, d184595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d182790 q = 1) : d184596 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d182790, d184596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182790, d184596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182791 q = 1) : d184597 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d182791, d184597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182791, d184597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16773 (p : Pattern) (selected : d182797 p = 1) : d184603 p = 1 := by
  have h0 (q : Pattern) (selected : d182117 q = 1) : d184520 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d182117, d184520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16721 q selected
    | true =>
      simp only [d182117, d184520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16729 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d182246 q = 1) : d184538 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d182246, d184538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182246, d184538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16739 q selected
  have h3 (q : Pattern) (selected : d182247 q = 1) : d184539 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d182247, d184539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182247, d184539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182426 q = 1) : d184557 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d182426, d184557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182426, d184557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16750 q selected
  have h5 (q : Pattern) (selected : d182427 q = 1) : d184558 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d182427, d184558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182427, d184558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182428 q = 1) : d184559 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d182428, d184559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182428, d184559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d182611 q = 1) : d184577 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d182611, d184577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182611, d184577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16761 q selected
  have h8 (q : Pattern) (selected : d182612 q = 1) : d184578 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d182612, d184578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182612, d184578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d182613 q = 1) : d184579 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d182613, d184579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182613, d184579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d182614 q = 1) : d184580 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d182614, d184580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182614, d184580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d182792 q = 1) : d184598 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d182792, d184598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182792, d184598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16772 q selected
  have h12 (q : Pattern) (selected : d182793 q = 1) : d184599 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d182793, d184599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182793, d184599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d182794 q = 1) : d184600 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d182794, d184600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182794, d184600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d182795 q = 1) : d184601 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d182795, d184601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182795, d184601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d182796 q = 1) : d184602 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d182796, d184602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d182796, d184602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d182797 q = 1) : d184603 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d182797, d184603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d182797, d184603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro16774 (p : Pattern) (selected : d182803 p = 1) : d184609 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182798 q = 1) : d184604 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d182798, d184604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16773 q selected
    | true =>
      simp only [d182798, d184604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182799 q = 1) : d184605 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d182799, d184605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182799, d184605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182800 q = 1) : d184606 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d182800, d184606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182800, d184606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182801 q = 1) : d184607 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d182801, d184607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182801, d184607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182802 q = 1) : d184608 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d182802, d184608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182802, d184608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182803 q = 1) : d184609 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d182803, d184609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182803, d184609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16775 (p : Pattern) (selected : d182809 p = 1) : d184615 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182804 q = 1) : d184610 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d182804, d184610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16774 q selected
    | true =>
      simp only [d182804, d184610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182805 q = 1) : d184611 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d182805, d184611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182805, d184611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182806 q = 1) : d184612 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d182806, d184612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182806, d184612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182807 q = 1) : d184613 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d182807, d184613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182807, d184613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182808 q = 1) : d184614 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d182808, d184614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182808, d184614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182809 q = 1) : d184615 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d182809, d184615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182809, d184615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16776 (p : Pattern) (selected : d182815 p = 1) : d184621 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182810 q = 1) : d184616 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d182810, d184616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16775 q selected
    | true =>
      simp only [d182810, d184616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182811 q = 1) : d184617 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d182811, d184617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182811, d184617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182812 q = 1) : d184618 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d182812, d184618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182812, d184618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182813 q = 1) : d184619 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d182813, d184619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182813, d184619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182814 q = 1) : d184620 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d182814, d184620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182814, d184620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182815 q = 1) : d184621 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d182815, d184621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182815, d184621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16777 (p : Pattern) (selected : d182821 p = 1) : d184627 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182816 q = 1) : d184622 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d182816, d184622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16776 q selected
    | true =>
      simp only [d182816, d184622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182817 q = 1) : d184623 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d182817, d184623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182817, d184623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182818 q = 1) : d184624 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d182818, d184624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182818, d184624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182819 q = 1) : d184625 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d182819, d184625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182819, d184625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182820 q = 1) : d184626 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d182820, d184626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182820, d184626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182821 q = 1) : d184627 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d182821, d184627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182821, d184627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16778 (p : Pattern) (selected : d182827 p = 1) : d184633 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182822 q = 1) : d184628 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d182822, d184628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16777 q selected
    | true =>
      simp only [d182822, d184628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182823 q = 1) : d184629 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d182823, d184629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182823, d184629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182824 q = 1) : d184630 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d182824, d184630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182824, d184630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182825 q = 1) : d184631 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d182825, d184631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182825, d184631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182826 q = 1) : d184632 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d182826, d184632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182826, d184632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182827 q = 1) : d184633 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d182827, d184633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182827, d184633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16779 (p : Pattern) (selected : d182833 p = 1) : d184639 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182828 q = 1) : d184634 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d182828, d184634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16778 q selected
    | true =>
      simp only [d182828, d184634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182829 q = 1) : d184635 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d182829, d184635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182829, d184635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182830 q = 1) : d184636 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d182830, d184636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182830, d184636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182831 q = 1) : d184637 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d182831, d184637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182831, d184637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182832 q = 1) : d184638 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d182832, d184638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182832, d184638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182833 q = 1) : d184639 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d182833, d184639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182833, d184639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16780 (p : Pattern) (selected : d182839 p = 1) : d184645 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182834 q = 1) : d184640 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d182834, d184640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16779 q selected
    | true =>
      simp only [d182834, d184640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182835 q = 1) : d184641 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d182835, d184641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182835, d184641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182836 q = 1) : d184642 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d182836, d184642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182836, d184642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182837 q = 1) : d184643 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d182837, d184643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182837, d184643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182838 q = 1) : d184644 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d182838, d184644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182838, d184644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182839 q = 1) : d184645 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d182839, d184645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182839, d184645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16781 (p : Pattern) (selected : d184680 p = 0) : d186173 p = 1 := by
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
  have h3 (q : Pattern) (selected : d27 q = 0) : d51879 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d184680 q = 0) : d186173 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d184680, d186173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d184680, d186173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16782 (p : Pattern) (selected : d184686 p = 0) : d186179 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184681 q = 0) : d186174 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d184681, d186174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16781 q selected
    | true =>
      simp only [d184681, d186174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d184682 q = 0) : d186175 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d184682, d186175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184682, d186175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184683 q = 0) : d186176 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d184683, d186176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184683, d186176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d184684 q = 0) : d186177 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d184684, d186177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d184684, d186177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d184685 q = 0) : d186178 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d184685, d186178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d184685, d186178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d184686 q = 0) : d186179 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d184686, d186179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d184686, d186179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16783 (p : Pattern) (selected : d184692 p = 0) : d186185 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184687 q = 0) : d186180 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d184687, d186180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16782 q selected
    | true =>
      simp only [d184687, d186180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d184688 q = 0) : d186181 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d184688, d186181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184688, d186181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184689 q = 0) : d186182 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d184689, d186182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d184689, d186182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d184690 q = 0) : d186183 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d184690, d186183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d184690, d186183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d184691 q = 0) : d186184 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d184691, d186184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d184691, d186184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d184692 q = 0) : d186185 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d184692, d186185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184692, d186185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16784 (p : Pattern) (selected : d184698 p = 0) : d186191 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184693 q = 0) : d186186 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184693, d186186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16783 q selected
    | true =>
      simp only [d184693, d186186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d184694 q = 0) : d186187 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184694, d186187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d184694, d186187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d184695 q = 0) : d186188 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d184695, d186188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d184695, d186188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d184696 q = 0) : d186189 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d184696, d186189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184696, d186189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d184697 q = 0) : d186190 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d184697, d186190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184697, d186190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d184698 q = 0) : d186191 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d184698, d186191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184698, d186191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16785 (p : Pattern) (selected : d184699 p = 0) : d186192 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184687 q = 0) : d186180 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d184687, d186180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16782 q selected
    | true =>
      simp only [d184687, d186180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d184688 q = 0) : d186181 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d184688, d186181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184688, d186181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184689 q = 0) : d186182 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d184689, d186182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d184689, d186182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d184690 q = 0) : d186183 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d184690, d186183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d184690, d186183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d184691 q = 0) : d186184 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d184691, d186184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d184691, d186184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d184699 q = 0) : d186192 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d184699, d186192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d184699, d186192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16786 (p : Pattern) (selected : d184705 p = 0) : d186198 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184693 q = 0) : d186186 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184693, d186186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16783 q selected
    | true =>
      simp only [d184693, d186186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d184694 q = 0) : d186187 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184694, d186187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d184694, d186187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d184695 q = 0) : d186188 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d184695, d186188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d184695, d186188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d184696 q = 0) : d186189 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d184696, d186189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184696, d186189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d184697 q = 0) : d186190 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d184697, d186190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184697, d186190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d184700 q = 0) : d186193 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184700, d186193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16785 q selected
    | true =>
      simp only [d184700, d186193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d184701 q = 0) : d186194 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184701, d186194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d184701, d186194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d184702 q = 0) : d186195 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d184702, d186195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d184702, d186195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d184703 q = 0) : d186196 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d184703, d186196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184703, d186196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d184704 q = 0) : d186197 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d184704, d186197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184704, d186197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d184705 q = 0) : d186198 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d184705, d186198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d184705, d186198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16787 (p : Pattern) (selected : d184710 p = 0) : d186203 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184700 q = 0) : d186193 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184700, d186193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16785 q selected
    | true =>
      simp only [d184700, d186193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d184701 q = 0) : d186194 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184701, d186194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d184701, d186194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d184702 q = 0) : d186195 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d184702, d186195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d184702, d186195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d184703 q = 0) : d186196 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d184703, d186196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184703, d186196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d184704 q = 0) : d186197 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d184704, d186197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184704, d186197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d184710 q = 0) : d186203 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d184710, d186203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184710, d186203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16788 (p : Pattern) (selected : d184716 p = 0) : d186209 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d66 q = 0) : d51918 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro187 q selected
  have h2 (q : Pattern) (selected : d25 q = 0) : d51877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro187 q selected
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d67 q = 0) : d51919 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d26 q = 0) : d51878 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d68 q = 0) : d51920 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d184716 q = 0) : d186209 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d184716, d186209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d184716, d186209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16789 (p : Pattern) (selected : d184722 p = 0) : d186215 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184717 q = 0) : d186210 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d184717, d186210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16788 q selected
    | true =>
      simp only [d184717, d186210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d184718 q = 0) : d186211 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d184718, d186211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184718, d186211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184719 q = 0) : d186212 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d184719, d186212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184719, d186212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d184720 q = 0) : d186213 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d184720, d186213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d184720, d186213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d184721 q = 0) : d186214 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d184721, d186214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d184721, d186214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d184722 q = 0) : d186215 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d184722, d186215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d184722, d186215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16790 (p : Pattern) (selected : d184728 p = 0) : d186221 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184723 q = 0) : d186216 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d184723, d186216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16789 q selected
    | true =>
      simp only [d184723, d186216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d184724 q = 0) : d186217 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d184724, d186217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184724, d186217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184725 q = 0) : d186218 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d184725, d186218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d184725, d186218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d184726 q = 0) : d186219 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d184726, d186219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d184726, d186219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d184727 q = 0) : d186220 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d184727, d186220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d184727, d186220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d184728 q = 0) : d186221 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d184728, d186221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d184728, d186221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16791 (p : Pattern) (selected : d184734 p = 0) : d186227 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184729 q = 0) : d186222 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184729, d186222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16790 q selected
    | true =>
      simp only [d184729, d186222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d184730 q = 0) : d186223 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184730, d186223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d184730, d186223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d184731 q = 0) : d186224 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d184731, d186224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d184731, d186224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d184732 q = 0) : d186225 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d184732, d186225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184732, d186225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d184733 q = 0) : d186226 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d184733, d186226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184733, d186226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d184734 q = 0) : d186227 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d184734, d186227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184734, d186227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16792 (p : Pattern) (selected : d184740 p = 0) : d186233 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184706 q = 0) : d186199 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d184706, d186199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16784 q selected
    | true =>
      simp only [d184706, d186199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16786 q selected
  have h2 (q : Pattern) (selected : d184707 q = 0) : d186200 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d184707, d186200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d184707, d186200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d184708 q = 0) : d186201 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d184708, d186201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d184708, d186201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d184709 q = 0) : d186202 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d184709, d186202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184709, d186202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d184711 q = 0) : d186204 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d184711, d186204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184711, d186204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16787 q selected
  have h6 (q : Pattern) (selected : d184712 q = 0) : d186205 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d184712, d186205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d184712, d186205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d184713 q = 0) : d186206 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d184713, d186206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d184713, d186206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d184714 q = 0) : d186207 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d184714, d186207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d184714, d186207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d184715 q = 0) : d186208 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d184715, d186208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d184715, d186208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d184735 q = 0) : d186228 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d184735, d186228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184735, d186228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16791 q selected
  have h11 (q : Pattern) (selected : d184736 q = 0) : d186229 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d184736, d186229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d184736, d186229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d184737 q = 0) : d186230 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d184737, d186230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d184737, d186230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d184738 q = 0) : d186231 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d184738, d186231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d184738, d186231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d184739 q = 0) : d186232 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d184739, d186232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d184739, d186232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d184740 q = 0) : d186233 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d184740, d186233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d184740, d186233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro16793 (p : Pattern) (selected : d184750 p = 0) : d186243 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184693 q = 0) : d186186 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184693, d186186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16783 q selected
    | true =>
      simp only [d184693, d186186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d184746 q = 0) : d186239 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184746, d186239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184746, d186239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184747 q = 0) : d186240 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d184747, d186240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d184747, d186240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d184748 q = 0) : d186241 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d184748, d186241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184748, d186241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d184749 q = 0) : d186242 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d184749, d186242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184749, d186242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d184750 q = 0) : d186243 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d184750, d186243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184750, d186243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16794 (p : Pattern) (selected : d184757 p = 0) : d186250 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184693 q = 0) : d186186 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184693, d186186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16783 q selected
    | true =>
      simp only [d184693, d186186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d184746 q = 0) : d186239 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184746, d186239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184746, d186239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184747 q = 0) : d186240 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d184747, d186240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d184747, d186240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d184748 q = 0) : d186241 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d184748, d186241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184748, d186241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d184749 q = 0) : d186242 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d184749, d186242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184749, d186242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d184700 q = 0) : d186193 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184700, d186193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16785 q selected
    | true =>
      simp only [d184700, d186193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d184753 q = 0) : d186246 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184753, d186246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184753, d186246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d184754 q = 0) : d186247 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d184754, d186247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d184754, d186247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d184755 q = 0) : d186248 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d184755, d186248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184755, d186248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d184756 q = 0) : d186249 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d184756, d186249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184756, d186249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d184757 q = 0) : d186250 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d184757, d186250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d184757, d186250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16795 (p : Pattern) (selected : d184762 p = 0) : d186255 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184687 q = 0) : d186180 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d184687, d186180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16782 q selected
    | true =>
      simp only [d184687, d186180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d184688 q = 0) : d186181 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d184688, d186181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184688, d186181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184689 q = 0) : d186182 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d184689, d186182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d184689, d186182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d184690 q = 0) : d186183 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d184690, d186183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d184690, d186183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d184761 q = 0) : d186254 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d184761, d186254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184761, d186254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d184762 q = 0) : d186255 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d184762, d186255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184762, d186255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16796 (p : Pattern) (selected : d184769 p = 0) : d186262 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184687 q = 0) : d186180 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d184687, d186180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16782 q selected
    | true =>
      simp only [d184687, d186180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d184688 q = 0) : d186181 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d184688, d186181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184688, d186181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184689 q = 0) : d186182 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d184689, d186182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d184689, d186182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d184767 q = 0) : d186260 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d184767, d186260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184767, d186260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d184768 q = 0) : d186261 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d184768, d186261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d184768, d186261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d184769 q = 0) : d186262 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d184769, d186262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184769, d186262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16797 (p : Pattern) (selected : d184773 p = 0) : d186266 p = 1 := by
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
  have h3 (q : Pattern) (selected : d141 q = 0) : d51992 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d141, d51992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d141, d51992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d25 q = 0) : d51877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro187 q selected
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d26 q = 0) : d51878 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d27 q = 0) : d51879 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d184773 q = 0) : d186266 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d184773, d186266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d184773, d186266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16798 (p : Pattern) (selected : d184779 p = 0) : d186272 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184774 q = 0) : d186267 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d184774, d186267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16797 q selected
    | true =>
      simp only [d184774, d186267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16781 q selected
  have h2 (q : Pattern) (selected : d184775 q = 0) : d186268 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d184775, d186268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184775, d186268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184776 q = 0) : d186269 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d184776, d186269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184776, d186269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d184681 q = 0) : d186174 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d184681, d186174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16781 q selected
    | true =>
      simp only [d184681, d186174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d184682 q = 0) : d186175 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d184682, d186175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184682, d186175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d184683 q = 0) : d186176 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d184683, d186176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184683, d186176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d184777 q = 0) : d186270 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d184777, d186270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d184777, d186270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d184684 q = 0) : d186177 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d184684, d186177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d184684, d186177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d184778 q = 0) : d186271 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d184778, d186271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d184778, d186271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d184779 q = 0) : d186272 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d184779, d186272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d184779, d186272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16799 (p : Pattern) (selected : d184785 p = 0) : d186278 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184780 q = 0) : d186273 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d184780, d186273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16798 q selected
    | true =>
      simp only [d184780, d186273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d184781 q = 0) : d186274 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d184781, d186274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184781, d186274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184687 q = 0) : d186180 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d184687, d186180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16782 q selected
    | true =>
      simp only [d184687, d186180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d184688 q = 0) : d186181 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d184688, d186181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184688, d186181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d184782 q = 0) : d186275 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d184782, d186275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d184782, d186275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d184783 q = 0) : d186276 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d184783, d186276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d184783, d186276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d184784 q = 0) : d186277 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d184784, d186277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d184784, d186277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d184785 q = 0) : d186278 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d184785, d186278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184785, d186278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16800 (p : Pattern) (selected : d184787 p = 0) : d186173 p = 1 := by
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
  have h3 (q : Pattern) (selected : d172 q = 0) : d51879 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d172, d51879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172, d51879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d184787 q = 0) : d186173 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d184787, d186173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d184787, d186173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16801 (p : Pattern) (selected : d184793 p = 0) : d186179 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184788 q = 0) : d186174 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d184788, d186174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16800 q selected
    | true =>
      simp only [d184788, d186174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d184789 q = 0) : d186175 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d184789, d186175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184789, d186175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184790 q = 0) : d186176 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d184790, d186176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184790, d186176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d184791 q = 0) : d186177 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d184791, d186177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d184791, d186177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d184792 q = 0) : d186178 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d184792, d186178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d184792, d186178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d184793 q = 0) : d186179 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d184793, d186179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d184793, d186179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16802 (p : Pattern) (selected : d184799 p = 0) : d186185 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184794 q = 0) : d186180 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d184794, d186180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16801 q selected
    | true =>
      simp only [d184794, d186180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d184795 q = 0) : d186181 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d184795, d186181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184795, d186181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184796 q = 0) : d186182 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d184796, d186182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d184796, d186182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d184797 q = 0) : d186183 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d184797, d186183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d184797, d186183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d184798 q = 0) : d186184 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d184798, d186184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d184798, d186184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d184799 q = 0) : d186185 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d184799, d186185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184799, d186185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16803 (p : Pattern) (selected : d184805 p = 0) : d186284 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184763 q = 0) : d186256 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184763, d186256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16795 q selected
    | true =>
      simp only [d184763, d186256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d184764 q = 0) : d186257 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184764, d186257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184764, d186257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184765 q = 0) : d186258 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d184765, d186258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d184765, d186258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d184766 q = 0) : d186259 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d184766, d186259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184766, d186259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d184770 q = 0) : d186263 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184770, d186263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16796 q selected
    | true =>
      simp only [d184770, d186263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d184771 q = 0) : d186264 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184771, d186264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184771, d186264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d184772 q = 0) : d186265 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d184772, d186265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d184772, d186265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d184786 q = 0) : d186279 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184786, d186279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16799 q selected
    | true =>
      simp only [d184786, d186279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16783 q selected
  have h9 (q : Pattern) (selected : d184800 q = 0) : d186186 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184800, d186186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16802 q selected
    | true =>
      simp only [d184800, d186186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d184801 q = 0) : d186280 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184801, d186280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d184801, d186280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d184693 q = 0) : d186186 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184693, d186186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16783 q selected
    | true =>
      simp only [d184693, d186186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d184694 q = 0) : d186187 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184694, d186187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d184694, d186187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d184802 q = 0) : d186281 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d184802, d186281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d184802, d186281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d184803 q = 0) : d186282 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d184803, d186282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d184803, d186282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d184804 q = 0) : d186283 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d184804, d186283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d184804, d186283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d184805 q = 0) : d186284 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d184805, d186284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184805, d186284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro16804 (p : Pattern) (selected : d184806 p = 0) : d186285 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184687 q = 0) : d186180 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d184687, d186180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16782 q selected
    | true =>
      simp only [d184687, d186180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d184688 q = 0) : d186181 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d184688, d186181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184688, d186181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184689 q = 0) : d186182 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d184689, d186182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d184689, d186182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d184690 q = 0) : d186183 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d184690, d186183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d184690, d186183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d184761 q = 0) : d186254 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d184761, d186254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184761, d186254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d184806 q = 0) : d186285 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d184806, d186285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d184806, d186285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16805 (p : Pattern) (selected : d184811 p = 0) : d186290 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184687 q = 0) : d186180 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d184687, d186180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16782 q selected
    | true =>
      simp only [d184687, d186180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d184688 q = 0) : d186181 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d184688, d186181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184688, d186181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184689 q = 0) : d186182 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d184689, d186182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d184689, d186182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d184767 q = 0) : d186260 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d184767, d186260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184767, d186260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d184768 q = 0) : d186261 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d184768, d186261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d184768, d186261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d184811 q = 0) : d186290 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d184811, d186290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d184811, d186290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16806 (p : Pattern) (selected : d184815 p = 0) : d186294 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184780 q = 0) : d186273 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d184780, d186273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16798 q selected
    | true =>
      simp only [d184780, d186273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d184781 q = 0) : d186274 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d184781, d186274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184781, d186274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184687 q = 0) : d186180 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d184687, d186180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16782 q selected
    | true =>
      simp only [d184687, d186180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d184688 q = 0) : d186181 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d184688, d186181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184688, d186181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d184782 q = 0) : d186275 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d184782, d186275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d184782, d186275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d184783 q = 0) : d186276 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d184783, d186276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d184783, d186276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d184784 q = 0) : d186277 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d184784, d186277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d184784, d186277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d184815 q = 0) : d186294 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d184815, d186294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d184815, d186294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16807 (p : Pattern) (selected : d184817 p = 0) : d186192 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184794 q = 0) : d186180 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d184794, d186180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16801 q selected
    | true =>
      simp only [d184794, d186180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d184795 q = 0) : d186181 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d184795, d186181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184795, d186181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184796 q = 0) : d186182 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d184796, d186182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d184796, d186182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d184797 q = 0) : d186183 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d184797, d186183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d184797, d186183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d184798 q = 0) : d186184 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d184798, d186184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d184798, d186184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d184817 q = 0) : d186192 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d184817, d186192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d184817, d186192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16808 (p : Pattern) (selected : d184823 p = 0) : d186300 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184763 q = 0) : d186256 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184763, d186256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16795 q selected
    | true =>
      simp only [d184763, d186256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d184764 q = 0) : d186257 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184764, d186257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184764, d186257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184765 q = 0) : d186258 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d184765, d186258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d184765, d186258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d184766 q = 0) : d186259 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d184766, d186259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184766, d186259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d184770 q = 0) : d186263 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184770, d186263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16796 q selected
    | true =>
      simp only [d184770, d186263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d184771 q = 0) : d186264 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184771, d186264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184771, d186264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d184772 q = 0) : d186265 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d184772, d186265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d184772, d186265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d184786 q = 0) : d186279 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184786, d186279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16799 q selected
    | true =>
      simp only [d184786, d186279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16783 q selected
  have h9 (q : Pattern) (selected : d184800 q = 0) : d186186 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184800, d186186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16802 q selected
    | true =>
      simp only [d184800, d186186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d184801 q = 0) : d186280 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184801, d186280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d184801, d186280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d184693 q = 0) : d186186 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184693, d186186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16783 q selected
    | true =>
      simp only [d184693, d186186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d184694 q = 0) : d186187 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184694, d186187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d184694, d186187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d184802 q = 0) : d186281 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d184802, d186281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d184802, d186281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d184803 q = 0) : d186282 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d184803, d186282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d184803, d186282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d184804 q = 0) : d186283 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d184804, d186283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d184804, d186283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d184807 q = 0) : d186286 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184807, d186286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16804 q selected
    | true =>
      simp only [d184807, d186286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d184808 q = 0) : d186287 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184808, d186287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184808, d186287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d184809 q = 0) : d186288 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d184809, d186288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d184809, d186288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d184810 q = 0) : d186289 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d184810, d186289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184810, d186289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d184812 q = 0) : d186291 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184812, d186291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16805 q selected
    | true =>
      simp only [d184812, d186291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d184813 q = 0) : d186292 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184813, d186292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184813, d186292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d184814 q = 0) : d186293 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d184814, d186293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d184814, d186293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d184816 q = 0) : d186295 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184816, d186295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16806 q selected
    | true =>
      simp only [d184816, d186295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16785 q selected
  have h24 (q : Pattern) (selected : d184818 q = 0) : d186193 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184818, d186193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16807 q selected
    | true =>
      simp only [d184818, d186193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d184819 q = 0) : d186296 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184819, d186296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d184819, d186296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d184700 q = 0) : d186193 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184700, d186193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16785 q selected
    | true =>
      simp only [d184700, d186193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d184701 q = 0) : d186194 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184701, d186194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d184701, d186194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d184820 q = 0) : d186297 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d184820, d186297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d184820, d186297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d184821 q = 0) : d186298 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d184821, d186298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d184821, d186298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d184822 q = 0) : d186299 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d184822, d186299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d184822, d186299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d184823 q = 0) : d186300 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d184823, d186300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d184823, d186300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro16809 (p : Pattern) (selected : d184825 p = 0) : d186302 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184693 q = 0) : d186186 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184693, d186186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16783 q selected
    | true =>
      simp only [d184693, d186186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d184746 q = 0) : d186239 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184746, d186239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184746, d186239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184747 q = 0) : d186240 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d184747, d186240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d184747, d186240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d184748 q = 0) : d186241 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d184748, d186241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184748, d186241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d184749 q = 0) : d186242 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d184749, d186242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184749, d186242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d184825 q = 0) : d186302 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d184825, d186302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d184825, d186302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16810 (p : Pattern) (selected : d184832 p = 0) : d186309 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184816 q = 0) : d186295 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184816, d186295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16806 q selected
    | true =>
      simp only [d184816, d186295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16785 q selected
  have h2 (q : Pattern) (selected : d184818 q = 0) : d186193 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184818, d186193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16807 q selected
    | true =>
      simp only [d184818, d186193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d184819 q = 0) : d186296 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184819, d186296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d184819, d186296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d184700 q = 0) : d186193 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184700, d186193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16785 q selected
    | true =>
      simp only [d184700, d186193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d184701 q = 0) : d186194 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184701, d186194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d184701, d186194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d184820 q = 0) : d186297 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d184820, d186297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d184820, d186297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d184830 q = 0) : d186307 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d184830, d186307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184830, d186307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d184831 q = 0) : d186308 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d184831, d186308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184831, d186308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d184832 q = 0) : d186309 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d184832, d186309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184832, d186309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro16811 (p : Pattern) (selected : d184838 p = 0) : d186315 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226 q = 0) : d52044 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d52044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226, d52044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro205 q selected
  have h2 (q : Pattern) (selected : d139 q = 0) : d51990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro205 q selected
    | true =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d227 q = 0) : d52045 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, d52045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d227, d52045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d140 q = 0) : d51991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228 q = 0) : d52046 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d52046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228, d52046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d66 q = 0) : d51918 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro187 q selected
  have h7 (q : Pattern) (selected : d25 q = 0) : d51877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro187 q selected
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d67 q = 0) : d51919 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d26 q = 0) : d51878 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d68 q = 0) : d51920 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d184838 q = 0) : d186315 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d184838, d186315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d184838, d186315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16812 (p : Pattern) (selected : d184844 p = 0) : d186321 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184839 q = 0) : d186316 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d184839, d186316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16811 q selected
    | true =>
      simp only [d184839, d186316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16788 q selected
  have h2 (q : Pattern) (selected : d184840 q = 0) : d186317 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d184840, d186317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184840, d186317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184841 q = 0) : d186318 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d184841, d186318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184841, d186318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d184717 q = 0) : d186210 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d184717, d186210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16788 q selected
    | true =>
      simp only [d184717, d186210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d184718 q = 0) : d186211 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d184718, d186211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184718, d186211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d184719 q = 0) : d186212 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d184719, d186212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184719, d186212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d184842 q = 0) : d186319 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d184842, d186319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d184842, d186319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d184720 q = 0) : d186213 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d184720, d186213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d184720, d186213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d184843 q = 0) : d186320 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d184843, d186320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d184843, d186320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d184844 q = 0) : d186321 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d184844, d186321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d184844, d186321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16813 (p : Pattern) (selected : d184850 p = 0) : d186327 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184845 q = 0) : d186322 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d184845, d186322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16812 q selected
    | true =>
      simp only [d184845, d186322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d184846 q = 0) : d186323 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d184846, d186323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184846, d186323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184723 q = 0) : d186216 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d184723, d186216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16789 q selected
    | true =>
      simp only [d184723, d186216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d184724 q = 0) : d186217 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d184724, d186217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184724, d186217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d184847 q = 0) : d186324 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d184847, d186324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d184847, d186324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d184848 q = 0) : d186325 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d184848, d186325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d184848, d186325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d184849 q = 0) : d186326 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d184849, d186326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d184849, d186326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d184850 q = 0) : d186327 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d184850, d186327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d184850, d186327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16814 (p : Pattern) (selected : d184852 p = 0) : d186209 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d245 q = 0) : d51918 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d245, d51918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d245, d51918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro210 q selected
  have h2 (q : Pattern) (selected : d170 q = 0) : d51877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d170, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro210 q selected
    | true =>
      simp only [d170, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d246 q = 0) : d51919 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246, d51919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246, d51919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d171 q = 0) : d51878 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d171, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d171, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d247 q = 0) : d51920 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247, d51920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d247, d51920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d184852 q = 0) : d186209 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d184852, d186209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d184852, d186209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16815 (p : Pattern) (selected : d184858 p = 0) : d186215 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184853 q = 0) : d186210 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d184853, d186210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16814 q selected
    | true =>
      simp only [d184853, d186210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d184854 q = 0) : d186211 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d184854, d186211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184854, d186211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184855 q = 0) : d186212 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d184855, d186212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184855, d186212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d184856 q = 0) : d186213 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d184856, d186213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d184856, d186213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d184857 q = 0) : d186214 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d184857, d186214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d184857, d186214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d184858 q = 0) : d186215 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d184858, d186215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d184858, d186215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16816 (p : Pattern) (selected : d184864 p = 0) : d186221 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184859 q = 0) : d186216 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d184859, d186216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16815 q selected
    | true =>
      simp only [d184859, d186216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d184860 q = 0) : d186217 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d184860, d186217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184860, d186217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184861 q = 0) : d186218 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d184861, d186218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d184861, d186218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d184862 q = 0) : d186219 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d184862, d186219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d184862, d186219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d184863 q = 0) : d186220 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d184863, d186220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d184863, d186220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d184864 q = 0) : d186221 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d184864, d186221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d184864, d186221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16817 (p : Pattern) (selected : d184870 p = 0) : d186333 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184851 q = 0) : d186328 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184851, d186328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16813 q selected
    | true =>
      simp only [d184851, d186328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16790 q selected
  have h2 (q : Pattern) (selected : d184865 q = 0) : d186222 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184865, d186222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16816 q selected
    | true =>
      simp only [d184865, d186222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d184866 q = 0) : d186329 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184866, d186329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d184866, d186329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d184729 q = 0) : d186222 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184729, d186222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16790 q selected
    | true =>
      simp only [d184729, d186222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d184730 q = 0) : d186223 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184730, d186223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d184730, d186223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d184867 q = 0) : d186330 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d184867, d186330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d184867, d186330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d184868 q = 0) : d186331 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d184868, d186331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184868, d186331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d184869 q = 0) : d186332 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d184869, d186332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184869, d186332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d184870 q = 0) : d186333 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d184870, d186333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184870, d186333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro16818 (p : Pattern) (selected : d184876 p = 0) : d186339 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184751 q = 0) : d186244 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d184751, d186244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184751, d186244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16793 q selected
  have h2 (q : Pattern) (selected : d184752 q = 0) : d186245 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d184752, d186245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d184752, d186245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d184758 q = 0) : d186251 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d184758, d186251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16793 q selected
    | true =>
      simp only [d184758, d186251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16794 q selected
  have h4 (q : Pattern) (selected : d184759 q = 0) : d186252 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d184759, d186252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d184759, d186252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d184760 q = 0) : d186253 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d184760, d186253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d184760, d186253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d184824 q = 0) : d186301 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d184824, d186301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16803 q selected
    | true =>
      simp only [d184824, d186301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16808 q selected
  have h7 (q : Pattern) (selected : d184826 q = 0) : d186303 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d184826, d186303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16809 q selected
    | true =>
      simp only [d184826, d186303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d184827 q = 0) : d186304 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d184827, d186304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d184827, d186304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d184828 q = 0) : d186305 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d184828, d186305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d184828, d186305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d184829 q = 0) : d186306 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d184829, d186306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d184829, d186306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d184833 q = 0) : d186310 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d184833, d186310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184833, d186310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16810 q selected
  have h12 (q : Pattern) (selected : d184834 q = 0) : d186311 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d184834, d186311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d184834, d186311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d184835 q = 0) : d186312 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d184835, d186312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d184835, d186312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d184836 q = 0) : d186313 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d184836, d186313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d184836, d186313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d184837 q = 0) : d186314 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d184837, d186314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d184837, d186314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d184871 q = 0) : d186334 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d184871, d186334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184871, d186334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16817 q selected
  have h17 (q : Pattern) (selected : d184872 q = 0) : d186335 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d184872, d186335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d184872, d186335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d184873 q = 0) : d186336 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d184873, d186336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d184873, d186336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d184874 q = 0) : d186337 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d184874, d186337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d184874, d186337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d184875 q = 0) : d186338 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d184875, d186338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d184875, d186338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d184876 q = 0) : d186339 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d184876, d186339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d184876, d186339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro16819 (p : Pattern) (selected : d184882 p = 0) : d186345 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184741 q = 0) : d186234 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d184741, d186234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184741, d186234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16792 q selected
  have h2 (q : Pattern) (selected : d184742 q = 0) : d186235 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d184742, d186235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184742, d186235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184743 q = 0) : d186236 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d184743, d186236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184743, d186236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d184744 q = 0) : d186237 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d184744, d186237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184744, d186237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d184745 q = 0) : d186238 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d184745, d186238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184745, d186238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d184877 q = 0) : d186340 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d184877, d186340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184877, d186340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16818 q selected
  have h7 (q : Pattern) (selected : d184878 q = 0) : d186341 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d184878, d186341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184878, d186341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d184879 q = 0) : d186342 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d184879, d186342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184879, d186342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d184880 q = 0) : d186343 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d184880, d186343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184880, d186343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d184881 q = 0) : d186344 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d184881, d186344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184881, d186344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d184882 q = 0) : d186345 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d184882, d186345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d184882, d186345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16820 (p : Pattern) (selected : d184887 p = 0) : d186350 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184786 q = 0) : d186279 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184786, d186279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16799 q selected
    | true =>
      simp only [d184786, d186279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16783 q selected
  have h2 (q : Pattern) (selected : d184883 q = 0) : d186346 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184883, d186346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184883, d186346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184884 q = 0) : d186347 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d184884, d186347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d184884, d186347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d184885 q = 0) : d186348 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d184885, d186348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184885, d186348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d184886 q = 0) : d186349 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d184886, d186349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184886, d186349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d184887 q = 0) : d186350 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d184887, d186350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184887, d186350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16821 (p : Pattern) (selected : d184894 p = 0) : d186357 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184786 q = 0) : d186279 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184786, d186279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16799 q selected
    | true =>
      simp only [d184786, d186279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16783 q selected
  have h2 (q : Pattern) (selected : d184883 q = 0) : d186346 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184883, d186346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184883, d186346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184884 q = 0) : d186347 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d184884, d186347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d184884, d186347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d184885 q = 0) : d186348 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d184885, d186348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184885, d186348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d184886 q = 0) : d186349 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d184886, d186349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184886, d186349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d184816 q = 0) : d186295 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184816, d186295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16806 q selected
    | true =>
      simp only [d184816, d186295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16785 q selected
  have h7 (q : Pattern) (selected : d184890 q = 0) : d186353 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184890, d186353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184890, d186353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d184891 q = 0) : d186354 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d184891, d186354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d184891, d186354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d184892 q = 0) : d186355 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d184892, d186355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184892, d186355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d184893 q = 0) : d186356 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d184893, d186356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184893, d186356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d184894 q = 0) : d186357 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d184894, d186357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d184894, d186357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16822 (p : Pattern) (selected : d184899 p = 0) : d186362 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184780 q = 0) : d186273 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d184780, d186273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16798 q selected
    | true =>
      simp only [d184780, d186273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d184781 q = 0) : d186274 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d184781, d186274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184781, d186274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184687 q = 0) : d186180 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d184687, d186180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16782 q selected
    | true =>
      simp only [d184687, d186180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d184688 q = 0) : d186181 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d184688, d186181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184688, d186181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d184782 q = 0) : d186275 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d184782, d186275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d184782, d186275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d184783 q = 0) : d186276 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d184783, d186276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d184783, d186276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d184898 q = 0) : d186361 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d184898, d186361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184898, d186361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d184899 q = 0) : d186362 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d184899, d186362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184899, d186362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16823 (p : Pattern) (selected : d184906 p = 0) : d186369 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184780 q = 0) : d186273 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d184780, d186273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16798 q selected
    | true =>
      simp only [d184780, d186273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d184781 q = 0) : d186274 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d184781, d186274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184781, d186274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184687 q = 0) : d186180 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d184687, d186180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16782 q selected
    | true =>
      simp only [d184687, d186180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d184688 q = 0) : d186181 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d184688, d186181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184688, d186181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d184782 q = 0) : d186275 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d184782, d186275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d184782, d186275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d184904 q = 0) : d186367 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d184904, d186367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184904, d186367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d184905 q = 0) : d186368 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d184905, d186368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d184905, d186368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d184906 q = 0) : d186369 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d184906, d186369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184906, d186369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16824 (p : Pattern) (selected : d184910 p = 0) : d186373 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d9458 q = 0) : d101073 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9458, d101073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6619 q selected
    | true =>
      simp only [d9458, d101073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9460 q = 0) : d101075 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9460, d101075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9460, d101075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d16073 q = 0) : d126981 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16073, d126981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16073, d126981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9382 q = 0) : d101015 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6607 q selected
    | true =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d9384 q = 0) : d101017 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d101017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d9384, d101017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d12493 q = 0) : d112927 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, d112927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12493, d112927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d184910 q = 0) : d186373 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d184910, d186373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d184910, d186373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16825 (p : Pattern) (selected : d184916 p = 0) : d186379 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184911 q = 0) : d186374 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d184911, d186374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16824 q selected
    | true =>
      simp only [d184911, d186374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16797 q selected
  have h2 (q : Pattern) (selected : d184912 q = 0) : d186375 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d184912, d186375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184912, d186375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184913 q = 0) : d186376 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d184913, d186376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184913, d186376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d184774 q = 0) : d186267 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d184774, d186267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16797 q selected
    | true =>
      simp only [d184774, d186267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16781 q selected
  have h5 (q : Pattern) (selected : d184775 q = 0) : d186268 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d184775, d186268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184775, d186268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d184776 q = 0) : d186269 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d184776, d186269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184776, d186269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d184914 q = 0) : d186377 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d184914, d186377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d184914, d186377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d184681 q = 0) : d186174 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d184681, d186174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16781 q selected
    | true =>
      simp only [d184681, d186174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d184682 q = 0) : d186175 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d184682, d186175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184682, d186175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d184683 q = 0) : d186176 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d184683, d186176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184683, d186176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d184777 q = 0) : d186270 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d184777, d186270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d184777, d186270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d184915 q = 0) : d186378 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d184915, d186378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d184915, d186378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d184916 q = 0) : d186379 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d184916, d186379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d184916, d186379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro16826 (p : Pattern) (selected : d184922 p = 0) : d186385 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184917 q = 0) : d186380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d184917, d186380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16825 q selected
    | true =>
      simp only [d184917, d186380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d184918 q = 0) : d186381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d184918, d186381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184918, d186381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184780 q = 0) : d186273 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d184780, d186273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16798 q selected
    | true =>
      simp only [d184780, d186273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d184781 q = 0) : d186274 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d184781, d186274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184781, d186274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d184919 q = 0) : d186382 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d184919, d186382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d184919, d186382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d184920 q = 0) : d186383 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d184920, d186383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d184920, d186383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d184921 q = 0) : d186384 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d184921, d186384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d184921, d186384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d184922 q = 0) : d186385 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d184922, d186385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184922, d186385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16827 (p : Pattern) (selected : d184924 p = 0) : d186266 p = 1 := by
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
  have h3 (q : Pattern) (selected : d352 q = 0) : d51992 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352, d51992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352, d51992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d170 q = 0) : d51877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d170, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro210 q selected
    | true =>
      simp only [d170, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d171 q = 0) : d51878 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d171, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d171, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d172 q = 0) : d51879 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d172, d51879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172, d51879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d184924 q = 0) : d186266 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d184924, d186266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d184924, d186266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16828 (p : Pattern) (selected : d184930 p = 0) : d186272 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184925 q = 0) : d186267 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d184925, d186267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16827 q selected
    | true =>
      simp only [d184925, d186267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16800 q selected
  have h2 (q : Pattern) (selected : d184926 q = 0) : d186268 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d184926, d186268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184926, d186268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184927 q = 0) : d186269 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d184927, d186269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184927, d186269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d184788 q = 0) : d186174 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d184788, d186174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16800 q selected
    | true =>
      simp only [d184788, d186174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d184789 q = 0) : d186175 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d184789, d186175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184789, d186175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d184790 q = 0) : d186176 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d184790, d186176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184790, d186176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d184928 q = 0) : d186270 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d184928, d186270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d184928, d186270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d184791 q = 0) : d186177 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d184791, d186177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d184791, d186177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d184929 q = 0) : d186271 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d184929, d186271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d184929, d186271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d184930 q = 0) : d186272 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d184930, d186272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d184930, d186272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16829 (p : Pattern) (selected : d184936 p = 0) : d186278 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184931 q = 0) : d186273 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d184931, d186273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16828 q selected
    | true =>
      simp only [d184931, d186273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d184932 q = 0) : d186274 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d184932, d186274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184932, d186274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184794 q = 0) : d186180 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d184794, d186180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16801 q selected
    | true =>
      simp only [d184794, d186180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d184795 q = 0) : d186181 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d184795, d186181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184795, d186181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d184933 q = 0) : d186275 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d184933, d186275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d184933, d186275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d184934 q = 0) : d186276 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d184934, d186276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d184934, d186276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d184935 q = 0) : d186277 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d184935, d186277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d184935, d186277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d184936 q = 0) : d186278 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d184936, d186278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184936, d186278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16830 (p : Pattern) (selected : d184942 p = 0) : d186391 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184780 q = 0) : d186273 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d184780, d186273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16798 q selected
    | true =>
      simp only [d184780, d186273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d184781 q = 0) : d186274 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d184781, d186274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184781, d186274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184939 q = 0) : d186388 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d184939, d186388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d184939, d186388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d184940 q = 0) : d186389 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d184940, d186389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d184940, d186389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d184941 q = 0) : d186390 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d184941, d186390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d184941, d186390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d184942 q = 0) : d186391 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d184942, d186391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184942, d186391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16831 (p : Pattern) (selected : d184948 p = 0) : d186397 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184900 q = 0) : d186363 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184900, d186363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16822 q selected
    | true =>
      simp only [d184900, d186363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16795 q selected
  have h2 (q : Pattern) (selected : d184901 q = 0) : d186364 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184901, d186364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184901, d186364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184902 q = 0) : d186365 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d184902, d186365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d184902, d186365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d184903 q = 0) : d186366 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d184903, d186366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184903, d186366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d184907 q = 0) : d186370 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184907, d186370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16823 q selected
    | true =>
      simp only [d184907, d186370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16796 q selected
  have h6 (q : Pattern) (selected : d184908 q = 0) : d186371 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184908, d186371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184908, d186371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d184909 q = 0) : d186372 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d184909, d186372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d184909, d186372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d184923 q = 0) : d186386 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184923, d186386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16826 q selected
    | true =>
      simp only [d184923, d186386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16799 q selected
  have h9 (q : Pattern) (selected : d184937 q = 0) : d186279 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184937, d186279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16829 q selected
    | true =>
      simp only [d184937, d186279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16802 q selected
  have h10 (q : Pattern) (selected : d184938 q = 0) : d186387 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184938, d186387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d184938, d186387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d184943 q = 0) : d186392 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184943, d186392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16830 q selected
    | true =>
      simp only [d184943, d186392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d184944 q = 0) : d186393 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184944, d186393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d184944, d186393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d184945 q = 0) : d186394 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d184945, d186394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d184945, d186394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d184946 q = 0) : d186395 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d184946, d186395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d184946, d186395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d184947 q = 0) : d186396 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d184947, d186396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d184947, d186396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d184948 q = 0) : d186397 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d184948, d186397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184948, d186397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro16832 (p : Pattern) (selected : d184949 p = 0) : d186398 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184780 q = 0) : d186273 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d184780, d186273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16798 q selected
    | true =>
      simp only [d184780, d186273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d184781 q = 0) : d186274 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d184781, d186274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184781, d186274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184687 q = 0) : d186180 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d184687, d186180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16782 q selected
    | true =>
      simp only [d184687, d186180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d184688 q = 0) : d186181 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d184688, d186181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184688, d186181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d184782 q = 0) : d186275 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d184782, d186275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d184782, d186275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d184783 q = 0) : d186276 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d184783, d186276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d184783, d186276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d184898 q = 0) : d186361 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d184898, d186361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184898, d186361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d184949 q = 0) : d186398 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d184949, d186398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d184949, d186398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16833 (p : Pattern) (selected : d184954 p = 0) : d186403 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184780 q = 0) : d186273 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d184780, d186273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16798 q selected
    | true =>
      simp only [d184780, d186273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d184781 q = 0) : d186274 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d184781, d186274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184781, d186274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184687 q = 0) : d186180 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d184687, d186180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16782 q selected
    | true =>
      simp only [d184687, d186180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d184688 q = 0) : d186181 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d184688, d186181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184688, d186181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d184782 q = 0) : d186275 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d184782, d186275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d184782, d186275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d184904 q = 0) : d186367 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d184904, d186367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184904, d186367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d184905 q = 0) : d186368 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d184905, d186368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d184905, d186368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d184954 q = 0) : d186403 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d184954, d186403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d184954, d186403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16834 (p : Pattern) (selected : d184958 p = 0) : d186407 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184917 q = 0) : d186380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d184917, d186380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16825 q selected
    | true =>
      simp only [d184917, d186380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d184918 q = 0) : d186381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d184918, d186381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184918, d186381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184780 q = 0) : d186273 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d184780, d186273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16798 q selected
    | true =>
      simp only [d184780, d186273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d184781 q = 0) : d186274 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d184781, d186274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184781, d186274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d184919 q = 0) : d186382 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d184919, d186382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d184919, d186382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d184920 q = 0) : d186383 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d184920, d186383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d184920, d186383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d184921 q = 0) : d186384 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d184921, d186384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d184921, d186384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d184958 q = 0) : d186407 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d184958, d186407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d184958, d186407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16835 (p : Pattern) (selected : d184960 p = 0) : d186294 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184931 q = 0) : d186273 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d184931, d186273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16828 q selected
    | true =>
      simp only [d184931, d186273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d184932 q = 0) : d186274 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d184932, d186274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184932, d186274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184794 q = 0) : d186180 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d184794, d186180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16801 q selected
    | true =>
      simp only [d184794, d186180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d184795 q = 0) : d186181 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d184795, d186181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184795, d186181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d184933 q = 0) : d186275 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d184933, d186275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d184933, d186275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d184934 q = 0) : d186276 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d184934, d186276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d184934, d186276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d184935 q = 0) : d186277 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d184935, d186277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d184935, d186277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d184960 q = 0) : d186294 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d184960, d186294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d184960, d186294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16836 (p : Pattern) (selected : d184963 p = 0) : d186410 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184780 q = 0) : d186273 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d184780, d186273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16798 q selected
    | true =>
      simp only [d184780, d186273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d184781 q = 0) : d186274 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d184781, d186274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184781, d186274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184939 q = 0) : d186388 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d184939, d186388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d184939, d186388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d184940 q = 0) : d186389 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d184940, d186389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d184940, d186389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d184941 q = 0) : d186390 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d184941, d186390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d184941, d186390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d184963 q = 0) : d186410 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d184963, d186410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d184963, d186410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16837 (p : Pattern) (selected : d184969 p = 0) : d186416 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184900 q = 0) : d186363 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184900, d186363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16822 q selected
    | true =>
      simp only [d184900, d186363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16795 q selected
  have h2 (q : Pattern) (selected : d184901 q = 0) : d186364 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184901, d186364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184901, d186364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184902 q = 0) : d186365 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d184902, d186365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d184902, d186365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d184903 q = 0) : d186366 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d184903, d186366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184903, d186366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d184907 q = 0) : d186370 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184907, d186370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16823 q selected
    | true =>
      simp only [d184907, d186370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16796 q selected
  have h6 (q : Pattern) (selected : d184908 q = 0) : d186371 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184908, d186371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184908, d186371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d184909 q = 0) : d186372 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d184909, d186372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d184909, d186372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d184923 q = 0) : d186386 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184923, d186386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16826 q selected
    | true =>
      simp only [d184923, d186386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16799 q selected
  have h9 (q : Pattern) (selected : d184937 q = 0) : d186279 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184937, d186279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16829 q selected
    | true =>
      simp only [d184937, d186279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16802 q selected
  have h10 (q : Pattern) (selected : d184938 q = 0) : d186387 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184938, d186387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d184938, d186387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d184943 q = 0) : d186392 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184943, d186392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16830 q selected
    | true =>
      simp only [d184943, d186392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d184944 q = 0) : d186393 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184944, d186393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d184944, d186393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d184945 q = 0) : d186394 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d184945, d186394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d184945, d186394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d184946 q = 0) : d186395 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d184946, d186395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d184946, d186395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d184947 q = 0) : d186396 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d184947, d186396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d184947, d186396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d184950 q = 0) : d186399 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184950, d186399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16832 q selected
    | true =>
      simp only [d184950, d186399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16804 q selected
  have h17 (q : Pattern) (selected : d184951 q = 0) : d186400 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184951, d186400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184951, d186400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d184952 q = 0) : d186401 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d184952, d186401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d184952, d186401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d184953 q = 0) : d186402 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d184953, d186402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184953, d186402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d184955 q = 0) : d186404 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184955, d186404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16833 q selected
    | true =>
      simp only [d184955, d186404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16805 q selected
  have h21 (q : Pattern) (selected : d184956 q = 0) : d186405 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184956, d186405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184956, d186405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d184957 q = 0) : d186406 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d184957, d186406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d184957, d186406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d184959 q = 0) : d186408 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184959, d186408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16834 q selected
    | true =>
      simp only [d184959, d186408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16806 q selected
  have h24 (q : Pattern) (selected : d184961 q = 0) : d186295 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184961, d186295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16835 q selected
    | true =>
      simp only [d184961, d186295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16807 q selected
  have h25 (q : Pattern) (selected : d184962 q = 0) : d186409 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184962, d186409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d184962, d186409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d184964 q = 0) : d186411 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184964, d186411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16836 q selected
    | true =>
      simp only [d184964, d186411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d184965 q = 0) : d186412 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184965, d186412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d184965, d186412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d184966 q = 0) : d186413 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d184966, d186413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d184966, d186413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d184967 q = 0) : d186414 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d184967, d186414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d184967, d186414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d184968 q = 0) : d186415 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d184968, d186415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d184968, d186415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d184969 q = 0) : d186416 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d184969, d186416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d184969, d186416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro16838 (p : Pattern) (selected : d184971 p = 0) : d186418 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184786 q = 0) : d186279 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184786, d186279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16799 q selected
    | true =>
      simp only [d184786, d186279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16783 q selected
  have h2 (q : Pattern) (selected : d184883 q = 0) : d186346 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184883, d186346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184883, d186346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184884 q = 0) : d186347 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d184884, d186347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d184884, d186347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d184885 q = 0) : d186348 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d184885, d186348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184885, d186348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d184886 q = 0) : d186349 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d184886, d186349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184886, d186349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d184693 q = 0) : d186186 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184693, d186186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16783 q selected
    | true =>
      simp only [d184693, d186186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d184746 q = 0) : d186239 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184746, d186239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184746, d186239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d184747 q = 0) : d186240 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d184747, d186240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d184747, d186240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d184748 q = 0) : d186241 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d184748, d186241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184748, d186241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d184749 q = 0) : d186242 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d184749, d186242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184749, d186242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d184971 q = 0) : d186418 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d184971, d186418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d184971, d186418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16839 (p : Pattern) (selected : d184978 p = 0) : d186425 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184959 q = 0) : d186408 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184959, d186408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16834 q selected
    | true =>
      simp only [d184959, d186408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16806 q selected
  have h2 (q : Pattern) (selected : d184961 q = 0) : d186295 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184961, d186295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16835 q selected
    | true =>
      simp only [d184961, d186295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16807 q selected
  have h3 (q : Pattern) (selected : d184962 q = 0) : d186409 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184962, d186409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d184962, d186409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d184964 q = 0) : d186411 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184964, d186411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16836 q selected
    | true =>
      simp only [d184964, d186411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d184965 q = 0) : d186412 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184965, d186412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d184965, d186412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d184966 q = 0) : d186413 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d184966, d186413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d184966, d186413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d184976 q = 0) : d186423 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d184976, d186423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184976, d186423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d184977 q = 0) : d186424 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d184977, d186424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184977, d186424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d184978 q = 0) : d186425 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d184978, d186425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184978, d186425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro16840 (p : Pattern) (selected : d184980 p = 0) : d186427 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184700 q = 0) : d186193 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184700, d186193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16785 q selected
    | true =>
      simp only [d184700, d186193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d184753 q = 0) : d186246 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184753, d186246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184753, d186246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184754 q = 0) : d186247 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d184754, d186247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d184754, d186247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d184755 q = 0) : d186248 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d184755, d186248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184755, d186248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d184756 q = 0) : d186249 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d184756, d186249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184756, d186249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d184980 q = 0) : d186427 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d184980, d186427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184980, d186427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16841 (p : Pattern) (selected : d184986 p = 0) : d186433 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d16156 q = 0) : d127047 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16156, d127047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16156, d127047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6619 q selected
  have h2 (q : Pattern) (selected : d9458 q = 0) : d101073 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9458, d101073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6619 q selected
    | true =>
      simp only [d9458, d101073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d16157 q = 0) : d127048 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16157, d127048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d16157, d127048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9460 q = 0) : d101075 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9460, d101075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9460, d101075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d16158 q = 0) : d127049 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16158, d127049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d16158, d127049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d12599 q = 0) : d113007 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d113007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12599, d113007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6607 q selected
  have h7 (q : Pattern) (selected : d9382 q = 0) : d101015 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6607 q selected
    | true =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d12600 q = 0) : d113008 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, d113008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d12600, d113008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d9384 q = 0) : d101017 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d101017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d9384, d101017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d12601 q = 0) : d113009 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12601, d113009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d12601, d113009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d184986 q = 0) : d186433 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d184986, d186433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d184986, d186433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16842 (p : Pattern) (selected : d184992 p = 0) : d186439 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184987 q = 0) : d186434 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d184987, d186434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16841 q selected
    | true =>
      simp only [d184987, d186434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16811 q selected
  have h2 (q : Pattern) (selected : d184988 q = 0) : d186435 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d184988, d186435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184988, d186435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184989 q = 0) : d186436 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d184989, d186436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184989, d186436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d184839 q = 0) : d186316 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d184839, d186316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16811 q selected
    | true =>
      simp only [d184839, d186316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16788 q selected
  have h5 (q : Pattern) (selected : d184840 q = 0) : d186317 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d184840, d186317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184840, d186317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d184841 q = 0) : d186318 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d184841, d186318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184841, d186318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d184990 q = 0) : d186437 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d184990, d186437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d184990, d186437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d184717 q = 0) : d186210 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d184717, d186210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16788 q selected
    | true =>
      simp only [d184717, d186210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d184718 q = 0) : d186211 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d184718, d186211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184718, d186211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d184719 q = 0) : d186212 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d184719, d186212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184719, d186212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d184842 q = 0) : d186319 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d184842, d186319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d184842, d186319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d184991 q = 0) : d186438 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d184991, d186438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d184991, d186438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d184992 q = 0) : d186439 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d184992, d186439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d184992, d186439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro16843 (p : Pattern) (selected : d184998 p = 0) : d186445 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184993 q = 0) : d186440 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d184993, d186440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16842 q selected
    | true =>
      simp only [d184993, d186440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d184994 q = 0) : d186441 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d184994, d186441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184994, d186441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184845 q = 0) : d186322 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d184845, d186322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16812 q selected
    | true =>
      simp only [d184845, d186322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d184846 q = 0) : d186323 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d184846, d186323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184846, d186323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d184995 q = 0) : d186442 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d184995, d186442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d184995, d186442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d184996 q = 0) : d186443 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d184996, d186443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d184996, d186443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d184997 q = 0) : d186444 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d184997, d186444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d184997, d186444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d184998 q = 0) : d186445 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d184998, d186445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d184998, d186445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16844 (p : Pattern) (selected : d185000 p = 0) : d186315 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d431 q = 0) : d52044 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d431, d52044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d431, d52044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro240 q selected
  have h2 (q : Pattern) (selected : d350 q = 0) : d51990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d350, d51990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro240 q selected
    | true =>
      simp only [d350, d51990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d432 q = 0) : d52045 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d432, d52045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d432, d52045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d351 q = 0) : d51991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d351, d51991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d351, d51991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d433 q = 0) : d52046 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d433, d52046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d433, d52046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d245 q = 0) : d51918 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d245, d51918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d245, d51918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro210 q selected
  have h7 (q : Pattern) (selected : d170 q = 0) : d51877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d170, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro210 q selected
    | true =>
      simp only [d170, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d246 q = 0) : d51919 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246, d51919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246, d51919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d171 q = 0) : d51878 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d171, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d171, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d247 q = 0) : d51920 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247, d51920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d247, d51920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d185000 q = 0) : d186315 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185000, d186315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185000, d186315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16845 (p : Pattern) (selected : d185006 p = 0) : d186321 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185001 q = 0) : d186316 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185001, d186316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16844 q selected
    | true =>
      simp only [d185001, d186316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16814 q selected
  have h2 (q : Pattern) (selected : d185002 q = 0) : d186317 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185002, d186317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185002, d186317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185003 q = 0) : d186318 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185003, d186318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185003, d186318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d184853 q = 0) : d186210 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d184853, d186210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16814 q selected
    | true =>
      simp only [d184853, d186210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d184854 q = 0) : d186211 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d184854, d186211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184854, d186211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d184855 q = 0) : d186212 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d184855, d186212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184855, d186212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185004 q = 0) : d186319 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185004, d186319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185004, d186319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d184856 q = 0) : d186213 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d184856, d186213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d184856, d186213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d185005 q = 0) : d186320 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d185005, d186320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185005, d186320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d185006 q = 0) : d186321 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d185006, d186321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d185006, d186321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16846 (p : Pattern) (selected : d185012 p = 0) : d186327 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185007 q = 0) : d186322 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185007, d186322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16845 q selected
    | true =>
      simp only [d185007, d186322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185008 q = 0) : d186323 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185008, d186323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185008, d186323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184859 q = 0) : d186216 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d184859, d186216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16815 q selected
    | true =>
      simp only [d184859, d186216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d184860 q = 0) : d186217 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d184860, d186217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184860, d186217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185009 q = 0) : d186324 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185009, d186324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185009, d186324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185010 q = 0) : d186325 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185010, d186325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185010, d186325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185011 q = 0) : d186326 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185011, d186326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185011, d186326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185012 q = 0) : d186327 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185012, d186327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185012, d186327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16847 (p : Pattern) (selected : d185018 p = 0) : d186451 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184845 q = 0) : d186322 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d184845, d186322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16812 q selected
    | true =>
      simp only [d184845, d186322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d184846 q = 0) : d186323 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d184846, d186323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184846, d186323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185015 q = 0) : d186448 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185015, d186448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185015, d186448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185016 q = 0) : d186449 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185016, d186449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185016, d186449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185017 q = 0) : d186450 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185017, d186450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185017, d186450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185018 q = 0) : d186451 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185018, d186451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185018, d186451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16848 (p : Pattern) (selected : d185024 p = 0) : d186457 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184999 q = 0) : d186446 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184999, d186446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16843 q selected
    | true =>
      simp only [d184999, d186446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16813 q selected
  have h2 (q : Pattern) (selected : d185013 q = 0) : d186328 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185013, d186328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16846 q selected
    | true =>
      simp only [d185013, d186328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16816 q selected
  have h3 (q : Pattern) (selected : d185014 q = 0) : d186447 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185014, d186447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d185014, d186447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185019 q = 0) : d186452 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185019, d186452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16847 q selected
    | true =>
      simp only [d185019, d186452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185020 q = 0) : d186453 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185020, d186453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185020, d186453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185021 q = 0) : d186454 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185021, d186454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185021, d186454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185022 q = 0) : d186455 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185022, d186455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185022, d186455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185023 q = 0) : d186456 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185023, d186456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185023, d186456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d185024 q = 0) : d186457 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d185024, d186457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185024, d186457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro16849 (p : Pattern) (selected : d185030 p = 0) : d186463 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184729 q = 0) : d186222 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184729, d186222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16790 q selected
    | true =>
      simp only [d184729, d186222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185026 q = 0) : d186459 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185026, d186459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185026, d186459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185027 q = 0) : d186460 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185027, d186460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185027, d186460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185028 q = 0) : d186461 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185028, d186461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185028, d186461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185029 q = 0) : d186462 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185029, d186462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185029, d186462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185030 q = 0) : d186463 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d185030, d186463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185030, d186463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16850 (p : Pattern) (selected : d185036 p = 0) : d186469 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d184888 q = 0) : d186351 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d184888, d186351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184888, d186351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16820 q selected
  have h2 (q : Pattern) (selected : d184889 q = 0) : d186352 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d184889, d186352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d184889, d186352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d184895 q = 0) : d186358 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d184895, d186358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16820 q selected
    | true =>
      simp only [d184895, d186358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16821 q selected
  have h4 (q : Pattern) (selected : d184896 q = 0) : d186359 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d184896, d186359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d184896, d186359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d184897 q = 0) : d186360 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d184897, d186360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d184897, d186360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d184970 q = 0) : d186417 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d184970, d186417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16831 q selected
    | true =>
      simp only [d184970, d186417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16837 q selected
  have h7 (q : Pattern) (selected : d184972 q = 0) : d186419 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d184972, d186419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16838 q selected
    | true =>
      simp only [d184972, d186419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16794 q selected
  have h8 (q : Pattern) (selected : d184973 q = 0) : d186420 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d184973, d186420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d184973, d186420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d184974 q = 0) : d186421 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d184974, d186421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d184974, d186421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d184975 q = 0) : d186422 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d184975, d186422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d184975, d186422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d184979 q = 0) : d186426 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d184979, d186426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184979, d186426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16839 q selected
  have h12 (q : Pattern) (selected : d184981 q = 0) : d186428 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d184981, d186428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184981, d186428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16840 q selected
  have h13 (q : Pattern) (selected : d184982 q = 0) : d186429 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d184982, d186429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d184982, d186429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d184983 q = 0) : d186430 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d184983, d186430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d184983, d186430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d184984 q = 0) : d186431 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d184984, d186431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d184984, d186431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d184985 q = 0) : d186432 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d184985, d186432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d184985, d186432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d185025 q = 0) : d186458 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d185025, d186458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185025, d186458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16848 q selected
  have h18 (q : Pattern) (selected : d185031 q = 0) : d186464 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d185031, d186464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185031, d186464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16849 q selected
  have h19 (q : Pattern) (selected : d185032 q = 0) : d186465 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d185032, d186465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d185032, d186465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d185033 q = 0) : d186466 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d185033, d186466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d185033, d186466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d185034 q = 0) : d186467 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d185034, d186467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d185034, d186467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d185035 q = 0) : d186468 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d185035, d186468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d185035, d186468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d185036 q = 0) : d186469 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d185036, d186469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d185036, d186469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro16851 (p : Pattern) (selected : d185042 p = 0) : d186475 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185037 q = 0) : d186470 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d185037, d186470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185037, d186470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16850 q selected
  have h2 (q : Pattern) (selected : d185038 q = 0) : d186471 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d185038, d186471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185038, d186471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185039 q = 0) : d186472 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d185039, d186472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185039, d186472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185040 q = 0) : d186473 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d185040, d186473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185040, d186473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185041 q = 0) : d186474 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d185041, d186474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185041, d186474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185042 q = 0) : d186475 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d185042, d186475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185042, d186475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16852 (p : Pattern) (selected : d185044 p = 0) : d186477 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d9458 q = 0) : d101073 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9458, d101073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6619 q selected
    | true =>
      simp only [d9458, d101073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9460 q = 0) : d101075 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9460, d101075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9460, d101075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d16073 q = 0) : d126981 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16073, d126981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16073, d126981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d751 q = 0) : d52428 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro317 q selected
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d752 q = 0) : d52429 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d753 q = 0) : d52430 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185044 q = 0) : d186477 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185044, d186477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185044, d186477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16853 (p : Pattern) (selected : d185045 p = 0) : d186478 p = 1 := by
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
  have h3 (q : Pattern) (selected : d753 q = 0) : d52430 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185045 q = 0) : d186478 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185045, d186478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185045, d186478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16854 (p : Pattern) (selected : d185055 p = 0) : d186488 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185046 q = 0) : d186479 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185046, d186479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16852 q selected
    | true =>
      simp only [d185046, d186479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16853 q selected
  have h2 (q : Pattern) (selected : d185047 q = 0) : d186480 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185047, d186480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185047, d186480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185048 q = 0) : d186481 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185048, d186481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185048, d186481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185049 q = 0) : d186482 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185049, d186482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16853 q selected
    | true =>
      simp only [d185049, d186482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185050 q = 0) : d186483 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185050, d186483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185050, d186483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185051 q = 0) : d186484 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185051, d186484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185051, d186484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185052 q = 0) : d186485 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185052, d186485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185052, d186485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185053 q = 0) : d186486 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185053, d186486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185053, d186486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d185054 q = 0) : d186487 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d185054, d186487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185054, d186487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d185055 q = 0) : d186488 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d185055, d186488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d185055, d186488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16855 (p : Pattern) (selected : d185059 p = 0) : d186492 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185049 q = 0) : d186482 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185049, d186482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16853 q selected
    | true =>
      simp only [d185049, d186482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185050 q = 0) : d186483 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185050, d186483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185050, d186483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185051 q = 0) : d186484 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185051, d186484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185051, d186484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185053 q = 0) : d186486 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185053, d186486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185053, d186486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185058 q = 0) : d186491 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d185058, d186491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185058, d186491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185059 q = 0) : d186492 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d185059, d186492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185059, d186492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16856 (p : Pattern) (selected : d185065 p = 0) : d186498 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185056 q = 0) : d186489 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185056, d186489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16854 q selected
    | true =>
      simp only [d185056, d186489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185057 q = 0) : d186490 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185057, d186490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185057, d186490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185060 q = 0) : d186493 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185060, d186493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16855 q selected
    | true =>
      simp only [d185060, d186493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185061 q = 0) : d186494 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185061, d186494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185061, d186494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185062 q = 0) : d186495 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185062, d186495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185062, d186495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185063 q = 0) : d186496 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185063, d186496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185063, d186496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185064 q = 0) : d186497 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185064, d186497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185064, d186497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185065 q = 0) : d186498 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185065, d186498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185065, d186498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16857 (p : Pattern) (selected : d185069 p = 0) : d186502 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185060 q = 0) : d186493 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185060, d186493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16855 q selected
    | true =>
      simp only [d185060, d186493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185061 q = 0) : d186494 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185061, d186494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185061, d186494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185066 q = 0) : d186499 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185066, d186499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185066, d186499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185067 q = 0) : d186500 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185067, d186500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185067, d186500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185068 q = 0) : d186501 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185068, d186501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185068, d186501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185069 q = 0) : d186502 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185069, d186502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185069, d186502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16858 (p : Pattern) (selected : d185075 p = 0) : d186508 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185070 q = 0) : d186503 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185070, d186503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16856 q selected
    | true =>
      simp only [d185070, d186503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16857 q selected
  have h2 (q : Pattern) (selected : d185071 q = 0) : d186504 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185071, d186504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185071, d186504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185072 q = 0) : d186505 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185072, d186505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185072, d186505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185073 q = 0) : d186506 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185073, d186506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185073, d186506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185074 q = 0) : d186507 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185074, d186507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185074, d186507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185075 q = 0) : d186508 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d185075, d186508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185075, d186508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16859 (p : Pattern) (selected : d185078 p = 0) : d186511 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185056 q = 0) : d186489 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185056, d186489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16854 q selected
    | true =>
      simp only [d185056, d186489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185057 q = 0) : d186490 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185057, d186490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185057, d186490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185060 q = 0) : d186493 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185060, d186493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16855 q selected
    | true =>
      simp only [d185060, d186493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185061 q = 0) : d186494 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185061, d186494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185061, d186494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185062 q = 0) : d186495 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185062, d186495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185062, d186495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185063 q = 0) : d186496 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185063, d186496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185063, d186496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185064 q = 0) : d186497 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185064, d186497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185064, d186497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185078 q = 0) : d186511 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185078, d186511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185078, d186511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16860 (p : Pattern) (selected : d185079 p = 0) : d186512 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185060 q = 0) : d186493 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185060, d186493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16855 q selected
    | true =>
      simp only [d185060, d186493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185061 q = 0) : d186494 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185061, d186494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185061, d186494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185066 q = 0) : d186499 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185066, d186499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185066, d186499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185067 q = 0) : d186500 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185067, d186500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185067, d186500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185068 q = 0) : d186501 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185068, d186501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185068, d186501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185079 q = 0) : d186512 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185079, d186512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185079, d186512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16861 (p : Pattern) (selected : d185085 p = 0) : d186518 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185070 q = 0) : d186503 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185070, d186503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16856 q selected
    | true =>
      simp only [d185070, d186503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16857 q selected
  have h2 (q : Pattern) (selected : d185071 q = 0) : d186504 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185071, d186504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185071, d186504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185072 q = 0) : d186505 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185072, d186505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185072, d186505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185073 q = 0) : d186506 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185073, d186506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185073, d186506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185074 q = 0) : d186507 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185074, d186507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185074, d186507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185080 q = 0) : d186513 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185080, d186513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16859 q selected
    | true =>
      simp only [d185080, d186513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16860 q selected
  have h7 (q : Pattern) (selected : d185081 q = 0) : d186514 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185081, d186514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185081, d186514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185082 q = 0) : d186515 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185082, d186515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185082, d186515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d185083 q = 0) : d186516 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185083, d186516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185083, d186516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d185084 q = 0) : d186517 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185084, d186517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185084, d186517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d185085 q = 0) : d186518 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d185085, d186518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185085, d186518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16862 (p : Pattern) (selected : d185090 p = 0) : d186523 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185056 q = 0) : d186489 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185056, d186489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16854 q selected
    | true =>
      simp only [d185056, d186489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185057 q = 0) : d186490 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185057, d186490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185057, d186490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185060 q = 0) : d186493 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185060, d186493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16855 q selected
    | true =>
      simp only [d185060, d186493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185061 q = 0) : d186494 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185061, d186494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185061, d186494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185062 q = 0) : d186495 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185062, d186495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185062, d186495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185063 q = 0) : d186496 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185063, d186496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185063, d186496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185089 q = 0) : d186522 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185089, d186522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185089, d186522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185090 q = 0) : d186523 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185090, d186523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185090, d186523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16863 (p : Pattern) (selected : d185092 p = 0) : d186525 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185060 q = 0) : d186493 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185060, d186493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16855 q selected
    | true =>
      simp only [d185060, d186493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185061 q = 0) : d186494 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185061, d186494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185061, d186494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185066 q = 0) : d186499 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185066, d186499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185066, d186499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185067 q = 0) : d186500 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185067, d186500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185067, d186500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185091 q = 0) : d186524 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185091, d186524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185091, d186524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185092 q = 0) : d186525 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185092, d186525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185092, d186525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16864 (p : Pattern) (selected : d185099 p = 0) : d186532 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185056 q = 0) : d186489 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185056, d186489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16854 q selected
    | true =>
      simp only [d185056, d186489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185057 q = 0) : d186490 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185057, d186490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185057, d186490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185060 q = 0) : d186493 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185060, d186493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16855 q selected
    | true =>
      simp only [d185060, d186493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185061 q = 0) : d186494 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185061, d186494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185061, d186494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185062 q = 0) : d186495 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185062, d186495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185062, d186495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185097 q = 0) : d186530 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185097, d186530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185097, d186530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185098 q = 0) : d186531 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185098, d186531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185098, d186531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185099 q = 0) : d186532 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185099, d186532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185099, d186532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16865 (p : Pattern) (selected : d185102 p = 0) : d186535 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185060 q = 0) : d186493 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185060, d186493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16855 q selected
    | true =>
      simp only [d185060, d186493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185061 q = 0) : d186494 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185061, d186494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185061, d186494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185066 q = 0) : d186499 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185066, d186499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185066, d186499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185100 q = 0) : d186533 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185100, d186533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185100, d186533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185101 q = 0) : d186534 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185101, d186534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185101, d186534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185102 q = 0) : d186535 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185102, d186535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185102, d186535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16866 (p : Pattern) (selected : d185106 p = 0) : d186539 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d9587 q = 0) : d101167 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9587, d101167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6641 q selected
    | true =>
      simp only [d9587, d101167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9589 q = 0) : d101169 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9589, d101169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9589, d101169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d16270 q = 0) : d127147 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16270, d127147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16270, d127147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9468 q = 0) : d101083 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6620 q selected
    | true =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d9470 q = 0) : d101085 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d12748 q = 0) : d113134 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12748, d113134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12748, d113134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185106 q = 0) : d186539 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185106, d186539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185106, d186539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16867 (p : Pattern) (selected : d185112 p = 0) : d186545 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185107 q = 0) : d186540 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185107, d186540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16866 q selected
    | true =>
      simp only [d185107, d186540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16852 q selected
  have h2 (q : Pattern) (selected : d185108 q = 0) : d186541 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185108, d186541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185108, d186541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185109 q = 0) : d186542 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185109, d186542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185109, d186542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185046 q = 0) : d186479 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185046, d186479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16852 q selected
    | true =>
      simp only [d185046, d186479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16853 q selected
  have h5 (q : Pattern) (selected : d185047 q = 0) : d186480 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185047, d186480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185047, d186480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185048 q = 0) : d186481 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185048, d186481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185048, d186481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185110 q = 0) : d186543 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185110, d186543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185110, d186543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185049 q = 0) : d186482 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185049, d186482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16853 q selected
    | true =>
      simp only [d185049, d186482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d185050 q = 0) : d186483 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185050, d186483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185050, d186483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d185051 q = 0) : d186484 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185051, d186484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185051, d186484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d185052 q = 0) : d186485 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185052, d186485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185052, d186485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d185111 q = 0) : d186544 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d185111, d186544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185111, d186544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d185112 q = 0) : d186545 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d185112, d186545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d185112, d186545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro16868 (p : Pattern) (selected : d185118 p = 0) : d186551 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185113 q = 0) : d186546 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185113, d186546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16867 q selected
    | true =>
      simp only [d185113, d186546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185114 q = 0) : d186547 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185114, d186547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185114, d186547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185056 q = 0) : d186489 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185056, d186489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16854 q selected
    | true =>
      simp only [d185056, d186489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185057 q = 0) : d186490 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185057, d186490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185057, d186490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185115 q = 0) : d186548 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185115, d186548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185115, d186548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185116 q = 0) : d186549 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185116, d186549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185116, d186549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185117 q = 0) : d186550 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185117, d186550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185117, d186550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185118 q = 0) : d186551 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185118, d186551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185118, d186551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16869 (p : Pattern) (selected : d185120 p = 0) : d186477 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d9661 q = 0) : d101073 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9661, d101073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6654 q selected
    | true =>
      simp only [d9661, d101073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9663 q = 0) : d101075 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9663, d101075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9663, d101075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d16292 q = 0) : d126981 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16292, d126981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16292, d126981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d874 q = 0) : d52428 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d874, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro342 q selected
    | true =>
      simp only [d874, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d875 q = 0) : d52429 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d875, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d875, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d876 q = 0) : d52430 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d876, d52430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d876, d52430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185120 q = 0) : d186477 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185120, d186477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185120, d186477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16870 (p : Pattern) (selected : d185121 p = 0) : d186478 p = 1 := by
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
  have h3 (q : Pattern) (selected : d876 q = 0) : d52430 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d876, d52430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d876, d52430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185121 q = 0) : d186478 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185121, d186478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185121, d186478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16871 (p : Pattern) (selected : d185131 p = 0) : d186488 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185122 q = 0) : d186479 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185122, d186479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16869 q selected
    | true =>
      simp only [d185122, d186479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16870 q selected
  have h2 (q : Pattern) (selected : d185123 q = 0) : d186480 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185123, d186480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185123, d186480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185124 q = 0) : d186481 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185124, d186481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185124, d186481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185125 q = 0) : d186482 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185125, d186482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16870 q selected
    | true =>
      simp only [d185125, d186482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185126 q = 0) : d186483 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185126, d186483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185126, d186483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185127 q = 0) : d186484 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185127, d186484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185127, d186484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185128 q = 0) : d186485 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185128, d186485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185128, d186485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185129 q = 0) : d186486 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185129, d186486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185129, d186486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d185130 q = 0) : d186487 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d185130, d186487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185130, d186487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d185131 q = 0) : d186488 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d185131, d186488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d185131, d186488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16872 (p : Pattern) (selected : d185135 p = 0) : d186492 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185125 q = 0) : d186482 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185125, d186482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16870 q selected
    | true =>
      simp only [d185125, d186482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185126 q = 0) : d186483 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185126, d186483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185126, d186483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185127 q = 0) : d186484 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185127, d186484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185127, d186484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185129 q = 0) : d186486 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185129, d186486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185129, d186486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185134 q = 0) : d186491 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d185134, d186491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185134, d186491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185135 q = 0) : d186492 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d185135, d186492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185135, d186492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16873 (p : Pattern) (selected : d185141 p = 0) : d186498 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185132 q = 0) : d186489 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185132, d186489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16871 q selected
    | true =>
      simp only [d185132, d186489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185133 q = 0) : d186490 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185133, d186490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185133, d186490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185136 q = 0) : d186493 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185136, d186493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16872 q selected
    | true =>
      simp only [d185136, d186493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185137 q = 0) : d186494 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185137, d186494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185137, d186494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185138 q = 0) : d186495 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185138, d186495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185138, d186495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185139 q = 0) : d186496 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185139, d186496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185139, d186496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185140 q = 0) : d186497 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185140, d186497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185140, d186497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185141 q = 0) : d186498 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185141, d186498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185141, d186498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16874 (p : Pattern) (selected : d185145 p = 0) : d186502 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185136 q = 0) : d186493 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185136, d186493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16872 q selected
    | true =>
      simp only [d185136, d186493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185137 q = 0) : d186494 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185137, d186494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185137, d186494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185142 q = 0) : d186499 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185142, d186499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185142, d186499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185143 q = 0) : d186500 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185143, d186500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185143, d186500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185144 q = 0) : d186501 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185144, d186501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185144, d186501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185145 q = 0) : d186502 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185145, d186502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185145, d186502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16875 (p : Pattern) (selected : d185151 p = 0) : d186557 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185056 q = 0) : d186489 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185056, d186489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16854 q selected
    | true =>
      simp only [d185056, d186489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185057 q = 0) : d186490 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185057, d186490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185057, d186490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185148 q = 0) : d186554 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185148, d186554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185148, d186554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185149 q = 0) : d186555 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185149, d186555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185149, d186555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185150 q = 0) : d186556 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185150, d186556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185150, d186556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185151 q = 0) : d186557 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185151, d186557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185151, d186557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16876 (p : Pattern) (selected : d185157 p = 0) : d186563 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185093 q = 0) : d186526 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185093, d186526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16862 q selected
    | true =>
      simp only [d185093, d186526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16863 q selected
  have h2 (q : Pattern) (selected : d185094 q = 0) : d186527 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185094, d186527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185094, d186527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185095 q = 0) : d186528 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185095, d186528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185095, d186528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185096 q = 0) : d186529 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185096, d186529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185096, d186529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185103 q = 0) : d186536 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185103, d186536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16864 q selected
    | true =>
      simp only [d185103, d186536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16865 q selected
  have h6 (q : Pattern) (selected : d185104 q = 0) : d186537 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185104, d186537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185104, d186537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185105 q = 0) : d186538 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185105, d186538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185105, d186538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185119 q = 0) : d186552 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185119, d186552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16868 q selected
    | true =>
      simp only [d185119, d186552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16856 q selected
  have h9 (q : Pattern) (selected : d185146 q = 0) : d186503 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185146, d186503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16873 q selected
    | true =>
      simp only [d185146, d186503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16874 q selected
  have h10 (q : Pattern) (selected : d185147 q = 0) : d186553 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185147, d186553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d185147, d186553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d185152 q = 0) : d186558 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185152, d186558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16875 q selected
    | true =>
      simp only [d185152, d186558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d185153 q = 0) : d186559 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185153, d186559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d185153, d186559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d185154 q = 0) : d186560 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185154, d186560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d185154, d186560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d185155 q = 0) : d186561 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185155, d186561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185155, d186561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d185156 q = 0) : d186562 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185156, d186562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185156, d186562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d185157 q = 0) : d186563 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d185157, d186563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185157, d186563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro16877 (p : Pattern) (selected : d185158 p = 0) : d186564 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185056 q = 0) : d186489 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185056, d186489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16854 q selected
    | true =>
      simp only [d185056, d186489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185057 q = 0) : d186490 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185057, d186490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185057, d186490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185060 q = 0) : d186493 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185060, d186493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16855 q selected
    | true =>
      simp only [d185060, d186493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185061 q = 0) : d186494 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185061, d186494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185061, d186494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185062 q = 0) : d186495 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185062, d186495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185062, d186495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185063 q = 0) : d186496 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185063, d186496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185063, d186496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185089 q = 0) : d186522 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185089, d186522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185089, d186522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185158 q = 0) : d186564 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185158, d186564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185158, d186564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16878 (p : Pattern) (selected : d185159 p = 0) : d186565 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185060 q = 0) : d186493 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185060, d186493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16855 q selected
    | true =>
      simp only [d185060, d186493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185061 q = 0) : d186494 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185061, d186494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185061, d186494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185066 q = 0) : d186499 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185066, d186499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185066, d186499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185067 q = 0) : d186500 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185067, d186500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185067, d186500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185091 q = 0) : d186524 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185091, d186524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185091, d186524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185159 q = 0) : d186565 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185159, d186565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185159, d186565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16879 (p : Pattern) (selected : d185164 p = 0) : d186570 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185056 q = 0) : d186489 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185056, d186489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16854 q selected
    | true =>
      simp only [d185056, d186489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185057 q = 0) : d186490 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185057, d186490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185057, d186490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185060 q = 0) : d186493 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185060, d186493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16855 q selected
    | true =>
      simp only [d185060, d186493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185061 q = 0) : d186494 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185061, d186494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185061, d186494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185062 q = 0) : d186495 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185062, d186495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185062, d186495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185097 q = 0) : d186530 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185097, d186530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185097, d186530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185098 q = 0) : d186531 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185098, d186531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185098, d186531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185164 q = 0) : d186570 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185164, d186570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185164, d186570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16880 (p : Pattern) (selected : d185165 p = 0) : d186571 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185060 q = 0) : d186493 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185060, d186493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16855 q selected
    | true =>
      simp only [d185060, d186493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185061 q = 0) : d186494 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185061, d186494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185061, d186494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185066 q = 0) : d186499 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185066, d186499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185066, d186499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185100 q = 0) : d186533 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185100, d186533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185100, d186533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185101 q = 0) : d186534 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185101, d186534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185101, d186534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185165 q = 0) : d186571 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185165, d186571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185165, d186571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16881 (p : Pattern) (selected : d185169 p = 0) : d186575 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185113 q = 0) : d186546 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185113, d186546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16867 q selected
    | true =>
      simp only [d185113, d186546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185114 q = 0) : d186547 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185114, d186547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185114, d186547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185056 q = 0) : d186489 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185056, d186489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16854 q selected
    | true =>
      simp only [d185056, d186489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185057 q = 0) : d186490 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185057, d186490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185057, d186490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185115 q = 0) : d186548 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185115, d186548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185115, d186548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185116 q = 0) : d186549 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185116, d186549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185116, d186549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185117 q = 0) : d186550 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185117, d186550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185117, d186550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185169 q = 0) : d186575 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185169, d186575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185169, d186575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16882 (p : Pattern) (selected : d185171 p = 0) : d186511 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185132 q = 0) : d186489 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185132, d186489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16871 q selected
    | true =>
      simp only [d185132, d186489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185133 q = 0) : d186490 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185133, d186490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185133, d186490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185136 q = 0) : d186493 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185136, d186493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16872 q selected
    | true =>
      simp only [d185136, d186493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185137 q = 0) : d186494 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185137, d186494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185137, d186494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185138 q = 0) : d186495 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185138, d186495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185138, d186495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185139 q = 0) : d186496 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185139, d186496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185139, d186496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185140 q = 0) : d186497 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185140, d186497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185140, d186497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185171 q = 0) : d186511 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185171, d186511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185171, d186511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16883 (p : Pattern) (selected : d185172 p = 0) : d186512 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185136 q = 0) : d186493 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185136, d186493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16872 q selected
    | true =>
      simp only [d185136, d186493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185137 q = 0) : d186494 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185137, d186494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185137, d186494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185142 q = 0) : d186499 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185142, d186499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185142, d186499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185143 q = 0) : d186500 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185143, d186500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185143, d186500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185144 q = 0) : d186501 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185144, d186501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185144, d186501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185172 q = 0) : d186512 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185172, d186512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185172, d186512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16884 (p : Pattern) (selected : d185175 p = 0) : d186578 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185056 q = 0) : d186489 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185056, d186489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16854 q selected
    | true =>
      simp only [d185056, d186489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185057 q = 0) : d186490 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185057, d186490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185057, d186490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185148 q = 0) : d186554 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185148, d186554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185148, d186554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185149 q = 0) : d186555 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185149, d186555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185149, d186555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185150 q = 0) : d186556 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185150, d186556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185150, d186556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185175 q = 0) : d186578 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185175, d186578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185175, d186578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16885 (p : Pattern) (selected : d185181 p = 0) : d186584 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185093 q = 0) : d186526 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185093, d186526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16862 q selected
    | true =>
      simp only [d185093, d186526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16863 q selected
  have h2 (q : Pattern) (selected : d185094 q = 0) : d186527 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185094, d186527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185094, d186527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185095 q = 0) : d186528 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185095, d186528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185095, d186528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185096 q = 0) : d186529 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185096, d186529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185096, d186529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185103 q = 0) : d186536 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185103, d186536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16864 q selected
    | true =>
      simp only [d185103, d186536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16865 q selected
  have h6 (q : Pattern) (selected : d185104 q = 0) : d186537 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185104, d186537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185104, d186537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185105 q = 0) : d186538 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185105, d186538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185105, d186538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185119 q = 0) : d186552 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185119, d186552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16868 q selected
    | true =>
      simp only [d185119, d186552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16856 q selected
  have h9 (q : Pattern) (selected : d185146 q = 0) : d186503 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185146, d186503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16873 q selected
    | true =>
      simp only [d185146, d186503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16874 q selected
  have h10 (q : Pattern) (selected : d185147 q = 0) : d186553 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185147, d186553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d185147, d186553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d185152 q = 0) : d186558 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185152, d186558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16875 q selected
    | true =>
      simp only [d185152, d186558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d185153 q = 0) : d186559 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185153, d186559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d185153, d186559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d185154 q = 0) : d186560 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185154, d186560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d185154, d186560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d185155 q = 0) : d186561 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185155, d186561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185155, d186561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d185156 q = 0) : d186562 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185156, d186562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185156, d186562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d185160 q = 0) : d186566 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185160, d186566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16877 q selected
    | true =>
      simp only [d185160, d186566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16878 q selected
  have h17 (q : Pattern) (selected : d185161 q = 0) : d186567 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185161, d186567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185161, d186567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d185162 q = 0) : d186568 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185162, d186568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d185162, d186568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d185163 q = 0) : d186569 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185163, d186569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185163, d186569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d185166 q = 0) : d186572 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185166, d186572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16879 q selected
    | true =>
      simp only [d185166, d186572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16880 q selected
  have h21 (q : Pattern) (selected : d185167 q = 0) : d186573 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185167, d186573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185167, d186573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d185168 q = 0) : d186574 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185168, d186574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d185168, d186574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d185170 q = 0) : d186576 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185170, d186576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16881 q selected
    | true =>
      simp only [d185170, d186576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16859 q selected
  have h24 (q : Pattern) (selected : d185173 q = 0) : d186513 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185173, d186513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16882 q selected
    | true =>
      simp only [d185173, d186513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16883 q selected
  have h25 (q : Pattern) (selected : d185174 q = 0) : d186577 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185174, d186577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d185174, d186577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d185176 q = 0) : d186579 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185176, d186579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16884 q selected
    | true =>
      simp only [d185176, d186579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d185177 q = 0) : d186580 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185177, d186580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d185177, d186580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d185178 q = 0) : d186581 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185178, d186581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d185178, d186581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d185179 q = 0) : d186582 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185179, d186582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d185179, d186582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d185180 q = 0) : d186583 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185180, d186583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d185180, d186583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d185181 q = 0) : d186584 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d185181, d186584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d185181, d186584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro16886 (p : Pattern) (selected : d185188 p = 0) : d186591 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185070 q = 0) : d186503 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185070, d186503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16856 q selected
    | true =>
      simp only [d185070, d186503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16857 q selected
  have h2 (q : Pattern) (selected : d185071 q = 0) : d186504 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185071, d186504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185071, d186504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185072 q = 0) : d186505 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185072, d186505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185072, d186505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185073 q = 0) : d186506 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185073, d186506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185073, d186506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185074 q = 0) : d186507 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185074, d186507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185074, d186507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185183 q = 0) : d186586 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185183, d186586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16857 q selected
    | true =>
      simp only [d185183, d186586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185184 q = 0) : d186587 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185184, d186587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185184, d186587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185185 q = 0) : d186588 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185185, d186588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185185, d186588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d185186 q = 0) : d186589 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185186, d186589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185186, d186589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d185187 q = 0) : d186590 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185187, d186590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185187, d186590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d185188 q = 0) : d186591 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d185188, d186591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185188, d186591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16887 (p : Pattern) (selected : d185194 p = 0) : d186597 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185183 q = 0) : d186586 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185183, d186586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16857 q selected
    | true =>
      simp only [d185183, d186586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185184 q = 0) : d186587 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185184, d186587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185184, d186587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185185 q = 0) : d186588 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185185, d186588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185185, d186588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185186 q = 0) : d186589 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185186, d186589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185186, d186589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185187 q = 0) : d186590 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185187, d186590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185187, d186590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185189 q = 0) : d186592 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185189, d186592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16860 q selected
    | true =>
      simp only [d185189, d186592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185190 q = 0) : d186593 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185190, d186593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185190, d186593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185191 q = 0) : d186594 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185191, d186594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185191, d186594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d185192 q = 0) : d186595 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185192, d186595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185192, d186595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d185193 q = 0) : d186596 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185193, d186596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185193, d186596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d185194 q = 0) : d186597 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d185194, d186597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185194, d186597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16888 (p : Pattern) (selected : d185201 p = 0) : d186604 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185170 q = 0) : d186576 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185170, d186576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16881 q selected
    | true =>
      simp only [d185170, d186576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16859 q selected
  have h2 (q : Pattern) (selected : d185173 q = 0) : d186513 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185173, d186513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16882 q selected
    | true =>
      simp only [d185173, d186513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16883 q selected
  have h3 (q : Pattern) (selected : d185174 q = 0) : d186577 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185174, d186577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d185174, d186577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185176 q = 0) : d186579 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185176, d186579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16884 q selected
    | true =>
      simp only [d185176, d186579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185177 q = 0) : d186580 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185177, d186580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185177, d186580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185178 q = 0) : d186581 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185178, d186581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185178, d186581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185199 q = 0) : d186602 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185199, d186602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185199, d186602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185200 q = 0) : d186603 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185200, d186603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185200, d186603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d185201 q = 0) : d186604 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d185201, d186604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185201, d186604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro16889 (p : Pattern) (selected : d185203 p = 0) : d186606 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185189 q = 0) : d186592 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185189, d186592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16860 q selected
    | true =>
      simp only [d185189, d186592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185190 q = 0) : d186593 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185190, d186593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185190, d186593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185191 q = 0) : d186594 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185191, d186594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185191, d186594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185192 q = 0) : d186595 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185192, d186595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185192, d186595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185193 q = 0) : d186596 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185193, d186596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185193, d186596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185203 q = 0) : d186606 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d185203, d186606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185203, d186606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16890 (p : Pattern) (selected : d185209 p = 0) : d186612 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d16356 q = 0) : d127213 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16356, d127213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16356, d127213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6641 q selected
  have h2 (q : Pattern) (selected : d9587 q = 0) : d101167 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9587, d101167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6641 q selected
    | true =>
      simp only [d9587, d101167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d16357 q = 0) : d127214 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16357, d127214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d16357, d127214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9589 q = 0) : d101169 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9589, d101169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9589, d101169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d16358 q = 0) : d127215 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16358, d127215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d16358, d127215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d12858 q = 0) : d113214 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, d113214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12858, d113214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6620 q selected
  have h7 (q : Pattern) (selected : d9468 q = 0) : d101083 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6620 q selected
    | true =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d12859 q = 0) : d113215 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12859, d113215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d12859, d113215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d9470 q = 0) : d101085 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d12860 q = 0) : d113216 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12860, d113216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d12860, d113216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d185209 q = 0) : d186612 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185209, d186612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185209, d186612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16891 (p : Pattern) (selected : d185210 p = 0) : d186613 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d16156 q = 0) : d127047 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16156, d127047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16156, d127047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6619 q selected
  have h2 (q : Pattern) (selected : d9458 q = 0) : d101073 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9458, d101073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6619 q selected
    | true =>
      simp only [d9458, d101073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d16157 q = 0) : d127048 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16157, d127048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d16157, d127048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9460 q = 0) : d101075 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9460, d101075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9460, d101075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d16158 q = 0) : d127049 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16158, d127049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d16158, d127049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d971 q = 0) : d52590 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro317 q selected
  have h7 (q : Pattern) (selected : d751 q = 0) : d52428 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro317 q selected
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d972 q = 0) : d52591 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d752 q = 0) : d52429 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d973 q = 0) : d52592 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d52592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d973, d52592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d185210 q = 0) : d186613 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185210, d186613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185210, d186613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16892 (p : Pattern) (selected : d185214 p = 0) : d186617 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d971 q = 0) : d52590 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro317 q selected
  have h2 (q : Pattern) (selected : d751 q = 0) : d52428 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro317 q selected
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d972 q = 0) : d52591 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d752 q = 0) : d52429 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d973 q = 0) : d52592 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d52592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d973, d52592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185214 q = 0) : d186617 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185214, d186617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185214, d186617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16893 (p : Pattern) (selected : d185224 p = 0) : d186627 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185211 q = 0) : d186614 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185211, d186614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16890 q selected
    | true =>
      simp only [d185211, d186614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16891 q selected
  have h2 (q : Pattern) (selected : d185212 q = 0) : d186615 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185212, d186615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185212, d186615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185213 q = 0) : d186616 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185213, d186616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185213, d186616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185215 q = 0) : d186618 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185215, d186618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16891 q selected
    | true =>
      simp only [d185215, d186618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16892 q selected
  have h5 (q : Pattern) (selected : d185216 q = 0) : d186619 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185216, d186619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185216, d186619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185217 q = 0) : d186620 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185217, d186620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185217, d186620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185218 q = 0) : d186621 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185218, d186621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185218, d186621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185219 q = 0) : d186622 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185219, d186622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16892 q selected
    | true =>
      simp only [d185219, d186622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d185220 q = 0) : d186623 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185220, d186623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185220, d186623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d185221 q = 0) : d186624 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185221, d186624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185221, d186624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d185222 q = 0) : d186625 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185222, d186625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185222, d186625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d185223 q = 0) : d186626 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d185223, d186626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185223, d186626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d185224 q = 0) : d186627 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d185224, d186627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d185224, d186627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro16894 (p : Pattern) (selected : d185229 p = 0) : d186632 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185215 q = 0) : d186618 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185215, d186618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16891 q selected
    | true =>
      simp only [d185215, d186618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16892 q selected
  have h2 (q : Pattern) (selected : d185216 q = 0) : d186619 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185216, d186619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185216, d186619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185217 q = 0) : d186620 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185217, d186620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185217, d186620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185219 q = 0) : d186622 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185219, d186622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16892 q selected
    | true =>
      simp only [d185219, d186622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185220 q = 0) : d186623 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185220, d186623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185220, d186623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185221 q = 0) : d186624 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185221, d186624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185221, d186624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185222 q = 0) : d186625 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185222, d186625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185222, d186625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185227 q = 0) : d186630 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185227, d186630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185227, d186630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d185228 q = 0) : d186631 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d185228, d186631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185228, d186631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d185229 q = 0) : d186632 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d185229, d186632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d185229, d186632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16895 (p : Pattern) (selected : d185235 p = 0) : d186638 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185225 q = 0) : d186628 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185225, d186628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16893 q selected
    | true =>
      simp only [d185225, d186628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185226 q = 0) : d186629 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185226, d186629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185226, d186629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185230 q = 0) : d186633 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185230, d186633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16894 q selected
    | true =>
      simp only [d185230, d186633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185231 q = 0) : d186634 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185231, d186634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185231, d186634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185232 q = 0) : d186635 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185232, d186635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185232, d186635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185233 q = 0) : d186636 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185233, d186636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185233, d186636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185234 q = 0) : d186637 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185234, d186637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185234, d186637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185235 q = 0) : d186638 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185235, d186638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185235, d186638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16896 (p : Pattern) (selected : d185237 p = 0) : d186640 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185219 q = 0) : d186622 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185219, d186622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16892 q selected
    | true =>
      simp only [d185219, d186622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185220 q = 0) : d186623 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185220, d186623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185220, d186623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185221 q = 0) : d186624 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185221, d186624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185221, d186624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185227 q = 0) : d186630 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185227, d186630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185227, d186630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185236 q = 0) : d186639 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d185236, d186639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185236, d186639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185237 q = 0) : d186640 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d185237, d186640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185237, d186640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16897 (p : Pattern) (selected : d185243 p = 0) : d186646 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185230 q = 0) : d186633 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185230, d186633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16894 q selected
    | true =>
      simp only [d185230, d186633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185231 q = 0) : d186634 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185231, d186634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185231, d186634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185238 q = 0) : d186641 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185238, d186641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16896 q selected
    | true =>
      simp only [d185238, d186641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185239 q = 0) : d186642 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185239, d186642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185239, d186642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185240 q = 0) : d186643 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185240, d186643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185240, d186643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185241 q = 0) : d186644 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185241, d186644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185241, d186644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185242 q = 0) : d186645 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185242, d186645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185242, d186645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185243 q = 0) : d186646 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185243, d186646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185243, d186646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16898 (p : Pattern) (selected : d185245 p = 0) : d186613 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d16393 q = 0) : d127047 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16393, d127047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16393, d127047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6654 q selected
  have h2 (q : Pattern) (selected : d9661 q = 0) : d101073 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9661, d101073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6654 q selected
    | true =>
      simp only [d9661, d101073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d16394 q = 0) : d127048 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16394, d127048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d16394, d127048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9663 q = 0) : d101075 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9663, d101075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9663, d101075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d16395 q = 0) : d127049 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16395, d127049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d16395, d127049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1018 q = 0) : d52590 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1018, d52590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1018, d52590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro342 q selected
  have h7 (q : Pattern) (selected : d874 q = 0) : d52428 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d874, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro342 q selected
    | true =>
      simp only [d874, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d1019 q = 0) : d52591 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1019, d52591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1019, d52591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d875 q = 0) : d52429 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d875, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d875, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d1020 q = 0) : d52592 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1020, d52592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d1020, d52592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d185245 q = 0) : d186613 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185245, d186613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185245, d186613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16899 (p : Pattern) (selected : d185246 p = 0) : d186617 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1018 q = 0) : d52590 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1018, d52590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1018, d52590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro342 q selected
  have h2 (q : Pattern) (selected : d874 q = 0) : d52428 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d874, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro342 q selected
    | true =>
      simp only [d874, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1019 q = 0) : d52591 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1019, d52591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1019, d52591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d875 q = 0) : d52429 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d875, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d875, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1020 q = 0) : d52592 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1020, d52592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1020, d52592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185246 q = 0) : d186617 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185246, d186617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185246, d186617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16900 (p : Pattern) (selected : d185256 p = 0) : d186632 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185247 q = 0) : d186618 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185247, d186618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16898 q selected
    | true =>
      simp only [d185247, d186618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16899 q selected
  have h2 (q : Pattern) (selected : d185248 q = 0) : d186619 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185248, d186619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185248, d186619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185249 q = 0) : d186620 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185249, d186620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185249, d186620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185250 q = 0) : d186622 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185250, d186622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16899 q selected
    | true =>
      simp only [d185250, d186622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185251 q = 0) : d186623 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185251, d186623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185251, d186623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185252 q = 0) : d186624 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185252, d186624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185252, d186624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185253 q = 0) : d186625 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185253, d186625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185253, d186625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185254 q = 0) : d186630 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185254, d186630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185254, d186630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d185255 q = 0) : d186631 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d185255, d186631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185255, d186631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d185256 q = 0) : d186632 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d185256, d186632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d185256, d186632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16901 (p : Pattern) (selected : d185260 p = 0) : d186640 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185250 q = 0) : d186622 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185250, d186622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16899 q selected
    | true =>
      simp only [d185250, d186622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185251 q = 0) : d186623 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185251, d186623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185251, d186623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185252 q = 0) : d186624 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185252, d186624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185252, d186624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185254 q = 0) : d186630 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185254, d186630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185254, d186630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185259 q = 0) : d186639 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d185259, d186639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185259, d186639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185260 q = 0) : d186640 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d185260, d186640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185260, d186640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16902 (p : Pattern) (selected : d185266 p = 0) : d186646 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185257 q = 0) : d186633 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185257, d186633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16900 q selected
    | true =>
      simp only [d185257, d186633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185258 q = 0) : d186634 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185258, d186634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185258, d186634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185261 q = 0) : d186641 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185261, d186641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16901 q selected
    | true =>
      simp only [d185261, d186641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185262 q = 0) : d186642 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185262, d186642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185262, d186642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185263 q = 0) : d186643 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185263, d186643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185263, d186643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185264 q = 0) : d186644 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185264, d186644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185264, d186644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185265 q = 0) : d186645 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185265, d186645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185265, d186645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185266 q = 0) : d186646 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185266, d186646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185266, d186646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16903 (p : Pattern) (selected : d185270 p = 0) : d186651 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185261 q = 0) : d186641 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185261, d186641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16901 q selected
    | true =>
      simp only [d185261, d186641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185262 q = 0) : d186642 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185262, d186642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185262, d186642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185267 q = 0) : d186648 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185267, d186648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185267, d186648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185268 q = 0) : d186649 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185268, d186649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185268, d186649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185269 q = 0) : d186650 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185269, d186650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185269, d186650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185270 q = 0) : d186651 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185270, d186651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185270, d186651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16904 (p : Pattern) (selected : d185276 p = 0) : d186657 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185230 q = 0) : d186633 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185230, d186633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16894 q selected
    | true =>
      simp only [d185230, d186633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185231 q = 0) : d186634 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185231, d186634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185231, d186634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185273 q = 0) : d186654 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185273, d186654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185273, d186654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185274 q = 0) : d186655 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185274, d186655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185274, d186655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185275 q = 0) : d186656 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185275, d186656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185275, d186656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185276 q = 0) : d186657 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185276, d186657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185276, d186657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16905 (p : Pattern) (selected : d185282 p = 0) : d186663 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185244 q = 0) : d186647 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185244, d186647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16895 q selected
    | true =>
      simp only [d185244, d186647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16897 q selected
  have h2 (q : Pattern) (selected : d185271 q = 0) : d186652 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185271, d186652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16902 q selected
    | true =>
      simp only [d185271, d186652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16903 q selected
  have h3 (q : Pattern) (selected : d185272 q = 0) : d186653 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185272, d186653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d185272, d186653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185277 q = 0) : d186658 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185277, d186658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16904 q selected
    | true =>
      simp only [d185277, d186658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185278 q = 0) : d186659 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185278, d186659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185278, d186659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185279 q = 0) : d186660 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185279, d186660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185279, d186660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185280 q = 0) : d186661 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185280, d186661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185280, d186661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185281 q = 0) : d186662 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185281, d186662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185281, d186662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d185282 q = 0) : d186663 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d185282, d186663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185282, d186663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro16906 (p : Pattern) (selected : d185287 p = 0) : d186651 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185238 q = 0) : d186641 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185238, d186641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16896 q selected
    | true =>
      simp only [d185238, d186641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185239 q = 0) : d186642 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185239, d186642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185239, d186642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185284 q = 0) : d186648 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185284, d186648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185284, d186648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185285 q = 0) : d186649 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185285, d186649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185285, d186649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185286 q = 0) : d186650 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185286, d186650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185286, d186650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185287 q = 0) : d186651 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185287, d186651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185287, d186651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16907 (p : Pattern) (selected : d185293 p = 0) : d186670 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185288 q = 0) : d186665 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185288, d186665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16906 q selected
    | true =>
      simp only [d185288, d186665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185289 q = 0) : d186666 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185289, d186666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185289, d186666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185290 q = 0) : d186667 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185290, d186667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185290, d186667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185291 q = 0) : d186668 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185291, d186668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185291, d186668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185292 q = 0) : d186669 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185292, d186669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185292, d186669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185293 q = 0) : d186670 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d185293, d186670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185293, d186670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16908 (p : Pattern) (selected : d185299 p = 0) : d186676 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185076 q = 0) : d186509 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d185076, d186509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185076, d186509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16858 q selected
  have h2 (q : Pattern) (selected : d185077 q = 0) : d186510 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d185077, d186510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d185077, d186510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d185086 q = 0) : d186519 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d185086, d186519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16858 q selected
    | true =>
      simp only [d185086, d186519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16861 q selected
  have h4 (q : Pattern) (selected : d185087 q = 0) : d186520 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d185087, d186520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185087, d186520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185088 q = 0) : d186521 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d185088, d186521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185088, d186521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185182 q = 0) : d186585 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d185182, d186585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16876 q selected
    | true =>
      simp only [d185182, d186585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16885 q selected
  have h7 (q : Pattern) (selected : d185195 q = 0) : d186598 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d185195, d186598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16886 q selected
    | true =>
      simp only [d185195, d186598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16887 q selected
  have h8 (q : Pattern) (selected : d185196 q = 0) : d186599 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d185196, d186599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185196, d186599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d185197 q = 0) : d186600 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d185197, d186600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d185197, d186600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d185198 q = 0) : d186601 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d185198, d186601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185198, d186601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d185202 q = 0) : d186605 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d185202, d186605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185202, d186605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16888 q selected
  have h12 (q : Pattern) (selected : d185204 q = 0) : d186607 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d185204, d186607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185204, d186607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16889 q selected
  have h13 (q : Pattern) (selected : d185205 q = 0) : d186608 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d185205, d186608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d185205, d186608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d185206 q = 0) : d186609 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d185206, d186609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d185206, d186609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d185207 q = 0) : d186610 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d185207, d186610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d185207, d186610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d185208 q = 0) : d186611 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d185208, d186611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d185208, d186611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d185283 q = 0) : d186664 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d185283, d186664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185283, d186664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16905 q selected
  have h18 (q : Pattern) (selected : d185294 q = 0) : d186671 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d185294, d186671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185294, d186671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16907 q selected
  have h19 (q : Pattern) (selected : d185295 q = 0) : d186672 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d185295, d186672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d185295, d186672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d185296 q = 0) : d186673 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d185296, d186673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d185296, d186673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d185297 q = 0) : d186674 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d185297, d186674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d185297, d186674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d185298 q = 0) : d186675 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d185298, d186675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d185298, d186675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d185299 q = 0) : d186676 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d185299, d186676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d185299, d186676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro16909 (p : Pattern) (selected : d185305 p = 0) : d186682 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185300 q = 0) : d186677 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d185300, d186677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185300, d186677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16908 q selected
  have h2 (q : Pattern) (selected : d185301 q = 0) : d186678 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d185301, d186678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185301, d186678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185302 q = 0) : d186679 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d185302, d186679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185302, d186679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185303 q = 0) : d186680 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d185303, d186680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185303, d186680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185304 q = 0) : d186681 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d185304, d186681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185304, d186681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185305 q = 0) : d186682 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d185305, d186682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185305, d186682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16910 (p : Pattern) (selected : d185308 p = 0) : d186685 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d9789 q = 0) : d101310 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9789, d101310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6674 q selected
    | true =>
      simp only [d9789, d101310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9791 q = 0) : d101312 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9791, d101312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9791, d101312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d16438 q = 0) : d127276 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16438, d127276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16438, d127276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9800 q = 0) : d101321 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6675 q selected
    | true =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d9802 q = 0) : d101323 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9802, d101323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d9802, d101323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d14763 q = 0) : d122934 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14763, d122934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14763, d122934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185308 q = 0) : d186685 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185308, d186685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185308, d186685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16911 (p : Pattern) (selected : d185309 p = 0) : d186686 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1121 q = 0) : d52702 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro388 q selected
    | true =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1122 q = 0) : d52703 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1123 q = 0) : d52704 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1123, d52704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1123, d52704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185309 q = 0) : d186686 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185309, d186686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185309, d186686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16912 (p : Pattern) (selected : d185319 p = 0) : d186696 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185310 q = 0) : d186687 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185310, d186687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16910 q selected
    | true =>
      simp only [d185310, d186687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16911 q selected
  have h2 (q : Pattern) (selected : d185311 q = 0) : d186688 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185311, d186688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185311, d186688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185312 q = 0) : d186689 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185312, d186689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185312, d186689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185313 q = 0) : d186690 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185313, d186690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16911 q selected
    | true =>
      simp only [d185313, d186690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185314 q = 0) : d186691 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185314, d186691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185314, d186691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185315 q = 0) : d186692 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185315, d186692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185315, d186692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185316 q = 0) : d186693 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185316, d186693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185316, d186693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185317 q = 0) : d186694 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185317, d186694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185317, d186694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d185318 q = 0) : d186695 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d185318, d186695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185318, d186695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d185319 q = 0) : d186696 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d185319, d186696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d185319, d186696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16913 (p : Pattern) (selected : d185323 p = 0) : d186700 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185313 q = 0) : d186690 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185313, d186690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16911 q selected
    | true =>
      simp only [d185313, d186690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185314 q = 0) : d186691 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185314, d186691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185314, d186691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185315 q = 0) : d186692 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185315, d186692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185315, d186692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185317 q = 0) : d186694 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185317, d186694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185317, d186694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185322 q = 0) : d186699 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d185322, d186699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185322, d186699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185323 q = 0) : d186700 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d185323, d186700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185323, d186700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16914 (p : Pattern) (selected : d185329 p = 0) : d186706 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185320 q = 0) : d186697 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185320, d186697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16912 q selected
    | true =>
      simp only [d185320, d186697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185321 q = 0) : d186698 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185321, d186698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185321, d186698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185324 q = 0) : d186701 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185324, d186701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16913 q selected
    | true =>
      simp only [d185324, d186701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185325 q = 0) : d186702 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185325, d186702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185325, d186702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185326 q = 0) : d186703 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185326, d186703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185326, d186703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185327 q = 0) : d186704 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185327, d186704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185327, d186704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185328 q = 0) : d186705 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185328, d186705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185328, d186705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185329 q = 0) : d186706 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185329, d186706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185329, d186706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16915 (p : Pattern) (selected : d185333 p = 0) : d186710 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185324 q = 0) : d186701 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185324, d186701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16913 q selected
    | true =>
      simp only [d185324, d186701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185325 q = 0) : d186702 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185325, d186702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185325, d186702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185330 q = 0) : d186707 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185330, d186707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185330, d186707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185331 q = 0) : d186708 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185331, d186708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185331, d186708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185332 q = 0) : d186709 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185332, d186709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185332, d186709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185333 q = 0) : d186710 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185333, d186710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185333, d186710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16916 (p : Pattern) (selected : d185339 p = 0) : d186716 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185334 q = 0) : d186711 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185334, d186711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16914 q selected
    | true =>
      simp only [d185334, d186711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16915 q selected
  have h2 (q : Pattern) (selected : d185335 q = 0) : d186712 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185335, d186712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185335, d186712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185336 q = 0) : d186713 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185336, d186713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185336, d186713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185337 q = 0) : d186714 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185337, d186714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185337, d186714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185338 q = 0) : d186715 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185338, d186715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185338, d186715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185339 q = 0) : d186716 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d185339, d186716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185339, d186716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16917 (p : Pattern) (selected : d185342 p = 0) : d186719 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185320 q = 0) : d186697 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185320, d186697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16912 q selected
    | true =>
      simp only [d185320, d186697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185321 q = 0) : d186698 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185321, d186698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185321, d186698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185324 q = 0) : d186701 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185324, d186701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16913 q selected
    | true =>
      simp only [d185324, d186701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185325 q = 0) : d186702 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185325, d186702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185325, d186702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185326 q = 0) : d186703 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185326, d186703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185326, d186703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185327 q = 0) : d186704 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185327, d186704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185327, d186704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185328 q = 0) : d186705 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185328, d186705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185328, d186705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185342 q = 0) : d186719 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185342, d186719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185342, d186719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16918 (p : Pattern) (selected : d185343 p = 0) : d186720 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185324 q = 0) : d186701 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185324, d186701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16913 q selected
    | true =>
      simp only [d185324, d186701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185325 q = 0) : d186702 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185325, d186702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185325, d186702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185330 q = 0) : d186707 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185330, d186707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185330, d186707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185331 q = 0) : d186708 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185331, d186708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185331, d186708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185332 q = 0) : d186709 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185332, d186709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185332, d186709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185343 q = 0) : d186720 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185343, d186720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185343, d186720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16919 (p : Pattern) (selected : d185349 p = 0) : d186726 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185334 q = 0) : d186711 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185334, d186711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16914 q selected
    | true =>
      simp only [d185334, d186711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16915 q selected
  have h2 (q : Pattern) (selected : d185335 q = 0) : d186712 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185335, d186712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185335, d186712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185336 q = 0) : d186713 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185336, d186713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185336, d186713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185337 q = 0) : d186714 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185337, d186714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185337, d186714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185338 q = 0) : d186715 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185338, d186715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185338, d186715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185344 q = 0) : d186721 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185344, d186721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16917 q selected
    | true =>
      simp only [d185344, d186721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16918 q selected
  have h7 (q : Pattern) (selected : d185345 q = 0) : d186722 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185345, d186722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185345, d186722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185346 q = 0) : d186723 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185346, d186723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185346, d186723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d185347 q = 0) : d186724 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185347, d186724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185347, d186724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d185348 q = 0) : d186725 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185348, d186725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185348, d186725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d185349 q = 0) : d186726 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d185349, d186726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185349, d186726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16920 (p : Pattern) (selected : d185354 p = 0) : d186731 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185320 q = 0) : d186697 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185320, d186697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16912 q selected
    | true =>
      simp only [d185320, d186697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185321 q = 0) : d186698 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185321, d186698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185321, d186698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185324 q = 0) : d186701 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185324, d186701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16913 q selected
    | true =>
      simp only [d185324, d186701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185325 q = 0) : d186702 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185325, d186702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185325, d186702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185326 q = 0) : d186703 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185326, d186703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185326, d186703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185327 q = 0) : d186704 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185327, d186704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185327, d186704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185353 q = 0) : d186730 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185353, d186730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185353, d186730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185354 q = 0) : d186731 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185354, d186731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185354, d186731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16921 (p : Pattern) (selected : d185356 p = 0) : d186733 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185324 q = 0) : d186701 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185324, d186701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16913 q selected
    | true =>
      simp only [d185324, d186701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185325 q = 0) : d186702 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185325, d186702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185325, d186702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185330 q = 0) : d186707 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185330, d186707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185330, d186707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185331 q = 0) : d186708 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185331, d186708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185331, d186708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185355 q = 0) : d186732 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185355, d186732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185355, d186732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185356 q = 0) : d186733 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185356, d186733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185356, d186733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16922 (p : Pattern) (selected : d185363 p = 0) : d186740 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185320 q = 0) : d186697 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185320, d186697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16912 q selected
    | true =>
      simp only [d185320, d186697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185321 q = 0) : d186698 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185321, d186698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185321, d186698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185324 q = 0) : d186701 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185324, d186701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16913 q selected
    | true =>
      simp only [d185324, d186701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185325 q = 0) : d186702 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185325, d186702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185325, d186702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185326 q = 0) : d186703 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185326, d186703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185326, d186703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185361 q = 0) : d186738 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185361, d186738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185361, d186738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185362 q = 0) : d186739 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185362, d186739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185362, d186739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185363 q = 0) : d186740 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185363, d186740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185363, d186740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16923 (p : Pattern) (selected : d185366 p = 0) : d186743 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185324 q = 0) : d186701 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185324, d186701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16913 q selected
    | true =>
      simp only [d185324, d186701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185325 q = 0) : d186702 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185325, d186702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185325, d186702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185330 q = 0) : d186707 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185330, d186707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185330, d186707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185364 q = 0) : d186741 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185364, d186741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185364, d186741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185365 q = 0) : d186742 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185365, d186742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185365, d186742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185366 q = 0) : d186743 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185366, d186743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185366, d186743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16924 (p : Pattern) (selected : d185370 p = 0) : d186747 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d9753 q = 0) : d101274 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9753, d101274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6669 q selected
    | true =>
      simp only [d9753, d101274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9755 q = 0) : d101276 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9755, d101276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9755, d101276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d16507 q = 0) : d127345 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16507, d127345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16507, d127345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9778 q = 0) : d101299 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9778, d101299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6672 q selected
    | true =>
      simp only [d9778, d101299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d9780 q = 0) : d101301 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9780, d101301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d9780, d101301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d14758 q = 0) : d122929 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14758, d122929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14758, d122929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185370 q = 0) : d186747 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185370, d186747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185370, d186747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16925 (p : Pattern) (selected : d185374 p = 0) : d186751 p = 1 := by
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
  have h4 (q : Pattern) (selected : d185374 q = 0) : d186751 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185374, d186751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185374, d186751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16926 (p : Pattern) (selected : d185380 p = 0) : d186757 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185371 q = 0) : d186748 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185371, d186748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16924 q selected
    | true =>
      simp only [d185371, d186748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16910 q selected
  have h2 (q : Pattern) (selected : d185372 q = 0) : d186749 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185372, d186749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185372, d186749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185373 q = 0) : d186750 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185373, d186750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185373, d186750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185375 q = 0) : d186752 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185375, d186752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16910 q selected
    | true =>
      simp only [d185375, d186752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16925 q selected
  have h5 (q : Pattern) (selected : d185376 q = 0) : d186753 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185376, d186753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185376, d186753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185377 q = 0) : d186754 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185377, d186754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185377, d186754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185378 q = 0) : d186755 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185378, d186755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185378, d186755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185310 q = 0) : d186687 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185310, d186687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16910 q selected
    | true =>
      simp only [d185310, d186687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16911 q selected
  have h9 (q : Pattern) (selected : d185311 q = 0) : d186688 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185311, d186688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185311, d186688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d185312 q = 0) : d186689 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185312, d186689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185312, d186689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d185313 q = 0) : d186690 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185313, d186690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16911 q selected
    | true =>
      simp only [d185313, d186690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d185314 q = 0) : d186691 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185314, d186691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185314, d186691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d185315 q = 0) : d186692 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185315, d186692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185315, d186692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d185316 q = 0) : d186693 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185316, d186693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d185316, d186693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d185379 q = 0) : d186756 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d185379, d186756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185379, d186756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d185380 q = 0) : d186757 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d185380, d186757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d185380, d186757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro16927 (p : Pattern) (selected : d185386 p = 0) : d186763 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185381 q = 0) : d186758 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185381, d186758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16926 q selected
    | true =>
      simp only [d185381, d186758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185382 q = 0) : d186759 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185382, d186759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185382, d186759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185320 q = 0) : d186697 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185320, d186697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16912 q selected
    | true =>
      simp only [d185320, d186697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185321 q = 0) : d186698 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185321, d186698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185321, d186698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185383 q = 0) : d186760 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185383, d186760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185383, d186760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185384 q = 0) : d186761 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185384, d186761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185384, d186761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185385 q = 0) : d186762 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185385, d186762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185385, d186762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185386 q = 0) : d186763 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185386, d186763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185386, d186763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16928 (p : Pattern) (selected : d185388 p = 0) : d186685 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d9896 q = 0) : d101310 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9896, d101310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6690 q selected
    | true =>
      simp only [d9896, d101310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9898 q = 0) : d101312 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9898, d101312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9898, d101312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d16539 q = 0) : d127276 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16539, d127276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16539, d127276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9918 q = 0) : d101321 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9918, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6692 q selected
    | true =>
      simp only [d9918, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d9920 q = 0) : d101323 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9920, d101323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d9920, d101323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d14873 q = 0) : d122934 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14873, d122934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14873, d122934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185388 q = 0) : d186685 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185388, d186685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185388, d186685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16929 (p : Pattern) (selected : d185389 p = 0) : d186686 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1276 q = 0) : d52702 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1276, d52702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro417 q selected
    | true =>
      simp only [d1276, d52702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1277 q = 0) : d52703 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1277, d52703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1277, d52703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1278 q = 0) : d52704 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1278, d52704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1278, d52704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185389 q = 0) : d186686 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185389, d186686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185389, d186686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16930 (p : Pattern) (selected : d185399 p = 0) : d186696 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185390 q = 0) : d186687 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185390, d186687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16928 q selected
    | true =>
      simp only [d185390, d186687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16929 q selected
  have h2 (q : Pattern) (selected : d185391 q = 0) : d186688 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185391, d186688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185391, d186688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185392 q = 0) : d186689 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185392, d186689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185392, d186689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185393 q = 0) : d186690 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185393, d186690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16929 q selected
    | true =>
      simp only [d185393, d186690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185394 q = 0) : d186691 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185394, d186691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185394, d186691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185395 q = 0) : d186692 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185395, d186692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185395, d186692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185396 q = 0) : d186693 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185396, d186693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185396, d186693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185397 q = 0) : d186694 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185397, d186694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185397, d186694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d185398 q = 0) : d186695 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d185398, d186695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185398, d186695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d185399 q = 0) : d186696 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d185399, d186696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d185399, d186696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16931 (p : Pattern) (selected : d185403 p = 0) : d186700 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185393 q = 0) : d186690 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185393, d186690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16929 q selected
    | true =>
      simp only [d185393, d186690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185394 q = 0) : d186691 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185394, d186691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185394, d186691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185395 q = 0) : d186692 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185395, d186692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185395, d186692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185397 q = 0) : d186694 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185397, d186694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185397, d186694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185402 q = 0) : d186699 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d185402, d186699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185402, d186699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185403 q = 0) : d186700 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d185403, d186700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185403, d186700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16932 (p : Pattern) (selected : d185409 p = 0) : d186706 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185400 q = 0) : d186697 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185400, d186697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16930 q selected
    | true =>
      simp only [d185400, d186697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185401 q = 0) : d186698 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185401, d186698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185401, d186698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185404 q = 0) : d186701 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185404, d186701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16931 q selected
    | true =>
      simp only [d185404, d186701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185405 q = 0) : d186702 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185405, d186702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185405, d186702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185406 q = 0) : d186703 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185406, d186703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185406, d186703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185407 q = 0) : d186704 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185407, d186704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185407, d186704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185408 q = 0) : d186705 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185408, d186705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185408, d186705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185409 q = 0) : d186706 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185409, d186706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185409, d186706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16933 (p : Pattern) (selected : d185413 p = 0) : d186710 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185404 q = 0) : d186701 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185404, d186701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16931 q selected
    | true =>
      simp only [d185404, d186701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185405 q = 0) : d186702 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185405, d186702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185405, d186702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185410 q = 0) : d186707 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185410, d186707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185410, d186707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185411 q = 0) : d186708 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185411, d186708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185411, d186708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185412 q = 0) : d186709 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185412, d186709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185412, d186709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185413 q = 0) : d186710 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185413, d186710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185413, d186710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16934 (p : Pattern) (selected : d185419 p = 0) : d186769 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185320 q = 0) : d186697 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185320, d186697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16912 q selected
    | true =>
      simp only [d185320, d186697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185321 q = 0) : d186698 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185321, d186698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185321, d186698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185416 q = 0) : d186766 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185416, d186766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185416, d186766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185417 q = 0) : d186767 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185417, d186767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185417, d186767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185418 q = 0) : d186768 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185418, d186768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185418, d186768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185419 q = 0) : d186769 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185419, d186769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185419, d186769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16935 (p : Pattern) (selected : d185425 p = 0) : d186775 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185357 q = 0) : d186734 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185357, d186734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16920 q selected
    | true =>
      simp only [d185357, d186734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16921 q selected
  have h2 (q : Pattern) (selected : d185358 q = 0) : d186735 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185358, d186735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185358, d186735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185359 q = 0) : d186736 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185359, d186736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185359, d186736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185360 q = 0) : d186737 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185360, d186737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185360, d186737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185367 q = 0) : d186744 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185367, d186744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16922 q selected
    | true =>
      simp only [d185367, d186744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16923 q selected
  have h6 (q : Pattern) (selected : d185368 q = 0) : d186745 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185368, d186745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185368, d186745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185369 q = 0) : d186746 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185369, d186746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185369, d186746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185387 q = 0) : d186764 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185387, d186764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16927 q selected
    | true =>
      simp only [d185387, d186764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16914 q selected
  have h9 (q : Pattern) (selected : d185414 q = 0) : d186711 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185414, d186711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16932 q selected
    | true =>
      simp only [d185414, d186711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16933 q selected
  have h10 (q : Pattern) (selected : d185415 q = 0) : d186765 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185415, d186765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d185415, d186765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d185420 q = 0) : d186770 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185420, d186770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16934 q selected
    | true =>
      simp only [d185420, d186770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d185421 q = 0) : d186771 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185421, d186771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d185421, d186771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d185422 q = 0) : d186772 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185422, d186772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d185422, d186772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d185423 q = 0) : d186773 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185423, d186773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185423, d186773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d185424 q = 0) : d186774 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185424, d186774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185424, d186774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d185425 q = 0) : d186775 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d185425, d186775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185425, d186775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro16936 (p : Pattern) (selected : d185426 p = 0) : d186776 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185320 q = 0) : d186697 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185320, d186697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16912 q selected
    | true =>
      simp only [d185320, d186697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185321 q = 0) : d186698 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185321, d186698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185321, d186698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185324 q = 0) : d186701 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185324, d186701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16913 q selected
    | true =>
      simp only [d185324, d186701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185325 q = 0) : d186702 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185325, d186702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185325, d186702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185326 q = 0) : d186703 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185326, d186703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185326, d186703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185327 q = 0) : d186704 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185327, d186704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185327, d186704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185353 q = 0) : d186730 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185353, d186730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185353, d186730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185426 q = 0) : d186776 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185426, d186776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185426, d186776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16937 (p : Pattern) (selected : d185427 p = 0) : d186777 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185324 q = 0) : d186701 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185324, d186701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16913 q selected
    | true =>
      simp only [d185324, d186701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185325 q = 0) : d186702 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185325, d186702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185325, d186702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185330 q = 0) : d186707 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185330, d186707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185330, d186707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185331 q = 0) : d186708 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185331, d186708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185331, d186708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185355 q = 0) : d186732 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185355, d186732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185355, d186732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185427 q = 0) : d186777 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185427, d186777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185427, d186777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16938 (p : Pattern) (selected : d185432 p = 0) : d186782 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185320 q = 0) : d186697 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185320, d186697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16912 q selected
    | true =>
      simp only [d185320, d186697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185321 q = 0) : d186698 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185321, d186698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185321, d186698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185324 q = 0) : d186701 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185324, d186701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16913 q selected
    | true =>
      simp only [d185324, d186701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185325 q = 0) : d186702 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185325, d186702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185325, d186702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185326 q = 0) : d186703 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185326, d186703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185326, d186703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185361 q = 0) : d186738 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185361, d186738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185361, d186738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185362 q = 0) : d186739 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185362, d186739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185362, d186739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185432 q = 0) : d186782 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185432, d186782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185432, d186782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16939 (p : Pattern) (selected : d185433 p = 0) : d186783 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185324 q = 0) : d186701 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185324, d186701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16913 q selected
    | true =>
      simp only [d185324, d186701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185325 q = 0) : d186702 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185325, d186702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185325, d186702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185330 q = 0) : d186707 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185330, d186707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185330, d186707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185364 q = 0) : d186741 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185364, d186741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185364, d186741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185365 q = 0) : d186742 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185365, d186742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185365, d186742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185433 q = 0) : d186783 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185433, d186783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185433, d186783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16940 (p : Pattern) (selected : d185437 p = 0) : d186787 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185381 q = 0) : d186758 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185381, d186758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16926 q selected
    | true =>
      simp only [d185381, d186758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185382 q = 0) : d186759 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185382, d186759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185382, d186759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185320 q = 0) : d186697 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185320, d186697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16912 q selected
    | true =>
      simp only [d185320, d186697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185321 q = 0) : d186698 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185321, d186698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185321, d186698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185383 q = 0) : d186760 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185383, d186760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185383, d186760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185384 q = 0) : d186761 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185384, d186761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185384, d186761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185385 q = 0) : d186762 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185385, d186762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185385, d186762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185437 q = 0) : d186787 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185437, d186787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185437, d186787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16941 (p : Pattern) (selected : d185439 p = 0) : d186719 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185400 q = 0) : d186697 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185400, d186697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16930 q selected
    | true =>
      simp only [d185400, d186697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185401 q = 0) : d186698 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185401, d186698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185401, d186698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185404 q = 0) : d186701 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185404, d186701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16931 q selected
    | true =>
      simp only [d185404, d186701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185405 q = 0) : d186702 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185405, d186702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185405, d186702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185406 q = 0) : d186703 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185406, d186703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185406, d186703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185407 q = 0) : d186704 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185407, d186704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185407, d186704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185408 q = 0) : d186705 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185408, d186705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185408, d186705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185439 q = 0) : d186719 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185439, d186719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185439, d186719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16942 (p : Pattern) (selected : d185440 p = 0) : d186720 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185404 q = 0) : d186701 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185404, d186701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16931 q selected
    | true =>
      simp only [d185404, d186701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185405 q = 0) : d186702 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185405, d186702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185405, d186702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185410 q = 0) : d186707 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185410, d186707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185410, d186707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185411 q = 0) : d186708 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185411, d186708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185411, d186708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185412 q = 0) : d186709 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185412, d186709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185412, d186709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185440 q = 0) : d186720 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185440, d186720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185440, d186720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16943 (p : Pattern) (selected : d185443 p = 0) : d186790 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185320 q = 0) : d186697 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185320, d186697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16912 q selected
    | true =>
      simp only [d185320, d186697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185321 q = 0) : d186698 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185321, d186698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185321, d186698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185416 q = 0) : d186766 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185416, d186766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185416, d186766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185417 q = 0) : d186767 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185417, d186767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185417, d186767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185418 q = 0) : d186768 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185418, d186768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185418, d186768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185443 q = 0) : d186790 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185443, d186790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185443, d186790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16944 (p : Pattern) (selected : d185449 p = 0) : d186796 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185357 q = 0) : d186734 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185357, d186734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16920 q selected
    | true =>
      simp only [d185357, d186734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16921 q selected
  have h2 (q : Pattern) (selected : d185358 q = 0) : d186735 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185358, d186735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185358, d186735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185359 q = 0) : d186736 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185359, d186736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185359, d186736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185360 q = 0) : d186737 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185360, d186737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185360, d186737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185367 q = 0) : d186744 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185367, d186744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16922 q selected
    | true =>
      simp only [d185367, d186744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16923 q selected
  have h6 (q : Pattern) (selected : d185368 q = 0) : d186745 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185368, d186745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185368, d186745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185369 q = 0) : d186746 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185369, d186746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185369, d186746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185387 q = 0) : d186764 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185387, d186764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16927 q selected
    | true =>
      simp only [d185387, d186764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16914 q selected
  have h9 (q : Pattern) (selected : d185414 q = 0) : d186711 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185414, d186711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16932 q selected
    | true =>
      simp only [d185414, d186711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16933 q selected
  have h10 (q : Pattern) (selected : d185415 q = 0) : d186765 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185415, d186765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d185415, d186765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d185420 q = 0) : d186770 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185420, d186770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16934 q selected
    | true =>
      simp only [d185420, d186770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d185421 q = 0) : d186771 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185421, d186771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d185421, d186771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d185422 q = 0) : d186772 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185422, d186772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d185422, d186772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d185423 q = 0) : d186773 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185423, d186773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185423, d186773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d185424 q = 0) : d186774 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185424, d186774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185424, d186774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d185428 q = 0) : d186778 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185428, d186778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16936 q selected
    | true =>
      simp only [d185428, d186778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16937 q selected
  have h17 (q : Pattern) (selected : d185429 q = 0) : d186779 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185429, d186779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185429, d186779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d185430 q = 0) : d186780 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185430, d186780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d185430, d186780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d185431 q = 0) : d186781 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185431, d186781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185431, d186781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d185434 q = 0) : d186784 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185434, d186784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16938 q selected
    | true =>
      simp only [d185434, d186784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16939 q selected
  have h21 (q : Pattern) (selected : d185435 q = 0) : d186785 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185435, d186785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185435, d186785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d185436 q = 0) : d186786 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185436, d186786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d185436, d186786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d185438 q = 0) : d186788 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185438, d186788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16940 q selected
    | true =>
      simp only [d185438, d186788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16917 q selected
  have h24 (q : Pattern) (selected : d185441 q = 0) : d186721 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185441, d186721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16941 q selected
    | true =>
      simp only [d185441, d186721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16942 q selected
  have h25 (q : Pattern) (selected : d185442 q = 0) : d186789 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185442, d186789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d185442, d186789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d185444 q = 0) : d186791 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185444, d186791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16943 q selected
    | true =>
      simp only [d185444, d186791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d185445 q = 0) : d186792 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185445, d186792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d185445, d186792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d185446 q = 0) : d186793 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185446, d186793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d185446, d186793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d185447 q = 0) : d186794 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185447, d186794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d185447, d186794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d185448 q = 0) : d186795 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185448, d186795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d185448, d186795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d185449 q = 0) : d186796 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d185449, d186796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d185449, d186796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro16945 (p : Pattern) (selected : d185456 p = 0) : d186803 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185334 q = 0) : d186711 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185334, d186711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16914 q selected
    | true =>
      simp only [d185334, d186711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16915 q selected
  have h2 (q : Pattern) (selected : d185335 q = 0) : d186712 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185335, d186712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185335, d186712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185336 q = 0) : d186713 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185336, d186713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185336, d186713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185337 q = 0) : d186714 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185337, d186714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185337, d186714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185338 q = 0) : d186715 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185338, d186715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185338, d186715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185451 q = 0) : d186798 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185451, d186798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16915 q selected
    | true =>
      simp only [d185451, d186798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185452 q = 0) : d186799 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185452, d186799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185452, d186799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185453 q = 0) : d186800 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185453, d186800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185453, d186800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d185454 q = 0) : d186801 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185454, d186801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185454, d186801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d185455 q = 0) : d186802 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185455, d186802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185455, d186802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d185456 q = 0) : d186803 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d185456, d186803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185456, d186803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16946 (p : Pattern) (selected : d185462 p = 0) : d186809 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185451 q = 0) : d186798 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185451, d186798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16915 q selected
    | true =>
      simp only [d185451, d186798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185452 q = 0) : d186799 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185452, d186799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185452, d186799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185453 q = 0) : d186800 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185453, d186800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185453, d186800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185454 q = 0) : d186801 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185454, d186801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185454, d186801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185455 q = 0) : d186802 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185455, d186802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185455, d186802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185457 q = 0) : d186804 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185457, d186804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16918 q selected
    | true =>
      simp only [d185457, d186804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185458 q = 0) : d186805 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185458, d186805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185458, d186805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185459 q = 0) : d186806 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185459, d186806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185459, d186806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d185460 q = 0) : d186807 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185460, d186807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185460, d186807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d185461 q = 0) : d186808 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185461, d186808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185461, d186808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d185462 q = 0) : d186809 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d185462, d186809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185462, d186809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16947 (p : Pattern) (selected : d185469 p = 0) : d186816 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185438 q = 0) : d186788 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185438, d186788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16940 q selected
    | true =>
      simp only [d185438, d186788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16917 q selected
  have h2 (q : Pattern) (selected : d185441 q = 0) : d186721 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185441, d186721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16941 q selected
    | true =>
      simp only [d185441, d186721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16942 q selected
  have h3 (q : Pattern) (selected : d185442 q = 0) : d186789 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185442, d186789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d185442, d186789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185444 q = 0) : d186791 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185444, d186791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16943 q selected
    | true =>
      simp only [d185444, d186791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185445 q = 0) : d186792 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185445, d186792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185445, d186792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185446 q = 0) : d186793 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185446, d186793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185446, d186793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185467 q = 0) : d186814 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185467, d186814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185467, d186814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185468 q = 0) : d186815 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185468, d186815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185468, d186815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d185469 q = 0) : d186816 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d185469, d186816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185469, d186816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro16948 (p : Pattern) (selected : d185471 p = 0) : d186818 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185457 q = 0) : d186804 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185457, d186804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16918 q selected
    | true =>
      simp only [d185457, d186804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185458 q = 0) : d186805 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185458, d186805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185458, d186805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185459 q = 0) : d186806 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185459, d186806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185459, d186806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185460 q = 0) : d186807 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185460, d186807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185460, d186807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185461 q = 0) : d186808 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185461, d186808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185461, d186808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185471 q = 0) : d186818 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d185471, d186818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185471, d186818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16949 (p : Pattern) (selected : d185477 p = 0) : d186824 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d16649 q = 0) : d127450 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16649, d127450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16649, d127450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6669 q selected
  have h2 (q : Pattern) (selected : d9753 q = 0) : d101274 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9753, d101274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6669 q selected
    | true =>
      simp only [d9753, d101274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d16650 q = 0) : d127451 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16650, d127451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d16650, d127451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9755 q = 0) : d101276 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9755, d101276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9755, d101276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d16651 q = 0) : d127452 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16651, d127452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d16651, d127452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14994 q = 0) : d123119 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14994, d123119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14994, d123119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6672 q selected
  have h7 (q : Pattern) (selected : d9778 q = 0) : d101299 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9778, d101299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6672 q selected
    | true =>
      simp only [d9778, d101299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d14995 q = 0) : d123120 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14995, d123120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14995, d123120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d9780 q = 0) : d101301 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9780, d101301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d9780, d101301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d14996 q = 0) : d123121 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14996, d123121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d14996, d123121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d185477 q = 0) : d186824 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185477, d186824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185477, d186824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16950 (p : Pattern) (selected : d185478 p = 0) : d186825 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d16656 q = 0) : d127457 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16656, d127457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16656, d127457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6674 q selected
  have h2 (q : Pattern) (selected : d9789 q = 0) : d101310 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9789, d101310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6674 q selected
    | true =>
      simp only [d9789, d101310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d16657 q = 0) : d127458 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16657, d127458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d16657, d127458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9791 q = 0) : d101312 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9791, d101312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9791, d101312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d16658 q = 0) : d127459 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16658, d127459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d16658, d127459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15004 q = 0) : d123129 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15004, d123129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15004, d123129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6675 q selected
  have h7 (q : Pattern) (selected : d9800 q = 0) : d101321 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6675 q selected
    | true =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15005 q = 0) : d123130 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15005, d123130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15005, d123130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d9802 q = 0) : d101323 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9802, d101323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d9802, d101323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15006 q = 0) : d123131 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15006, d123131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d15006, d123131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d185478 q = 0) : d186825 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185478, d186825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185478, d186825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16951 (p : Pattern) (selected : d185482 p = 0) : d186829 p = 1 := by
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
  have h6 (q : Pattern) (selected : d185482 q = 0) : d186829 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185482, d186829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185482, d186829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16952 (p : Pattern) (selected : d185487 p = 0) : d186834 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1391 q = 0) : d52879 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1391, d52879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1391, d52879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro388 q selected
  have h2 (q : Pattern) (selected : d1121 q = 0) : d52702 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro388 q selected
    | true =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1392 q = 0) : d52880 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1392, d52880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1392, d52880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1122 q = 0) : d52703 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1393 q = 0) : d52881 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1393, d52881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1393, d52881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185487 q = 0) : d186834 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185487, d186834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185487, d186834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16953 (p : Pattern) (selected : d185496 p = 0) : d186843 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185479 q = 0) : d186826 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185479, d186826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16949 q selected
    | true =>
      simp only [d185479, d186826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16950 q selected
  have h2 (q : Pattern) (selected : d185480 q = 0) : d186827 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185480, d186827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185480, d186827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185481 q = 0) : d186828 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185481, d186828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185481, d186828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185483 q = 0) : d186830 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185483, d186830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16950 q selected
    | true =>
      simp only [d185483, d186830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16951 q selected
  have h5 (q : Pattern) (selected : d185484 q = 0) : d186831 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185484, d186831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185484, d186831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185485 q = 0) : d186832 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185485, d186832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185485, d186832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185486 q = 0) : d186833 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185486, d186833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185486, d186833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185488 q = 0) : d186835 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185488, d186835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16950 q selected
    | true =>
      simp only [d185488, d186835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16952 q selected
  have h9 (q : Pattern) (selected : d185489 q = 0) : d186836 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185489, d186836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185489, d186836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d185490 q = 0) : d186837 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185490, d186837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185490, d186837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d185491 q = 0) : d186838 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185491, d186838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16952 q selected
    | true =>
      simp only [d185491, d186838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d185492 q = 0) : d186839 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185492, d186839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185492, d186839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d185493 q = 0) : d186840 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185493, d186840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185493, d186840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d185494 q = 0) : d186841 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185494, d186841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d185494, d186841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d185495 q = 0) : d186842 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d185495, d186842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185495, d186842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d185496 q = 0) : d186843 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d185496, d186843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d185496, d186843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro16954 (p : Pattern) (selected : d185501 p = 0) : d186848 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185488 q = 0) : d186835 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185488, d186835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16950 q selected
    | true =>
      simp only [d185488, d186835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16952 q selected
  have h2 (q : Pattern) (selected : d185489 q = 0) : d186836 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185489, d186836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185489, d186836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185490 q = 0) : d186837 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185490, d186837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185490, d186837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185491 q = 0) : d186838 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185491, d186838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16952 q selected
    | true =>
      simp only [d185491, d186838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185492 q = 0) : d186839 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185492, d186839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185492, d186839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185493 q = 0) : d186840 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185493, d186840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185493, d186840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185494 q = 0) : d186841 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185494, d186841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185494, d186841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185499 q = 0) : d186846 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185499, d186846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185499, d186846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d185500 q = 0) : d186847 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d185500, d186847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185500, d186847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d185501 q = 0) : d186848 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d185501, d186848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d185501, d186848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16955 (p : Pattern) (selected : d185507 p = 0) : d186854 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185497 q = 0) : d186844 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185497, d186844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16953 q selected
    | true =>
      simp only [d185497, d186844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185498 q = 0) : d186845 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185498, d186845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185498, d186845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185502 q = 0) : d186849 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185502, d186849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16954 q selected
    | true =>
      simp only [d185502, d186849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185503 q = 0) : d186850 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185503, d186850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185503, d186850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185504 q = 0) : d186851 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185504, d186851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185504, d186851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185505 q = 0) : d186852 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185505, d186852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185505, d186852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185506 q = 0) : d186853 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185506, d186853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185506, d186853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185507 q = 0) : d186854 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185507, d186854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185507, d186854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16956 (p : Pattern) (selected : d185509 p = 0) : d186856 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185491 q = 0) : d186838 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185491, d186838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16952 q selected
    | true =>
      simp only [d185491, d186838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185492 q = 0) : d186839 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185492, d186839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185492, d186839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185493 q = 0) : d186840 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185493, d186840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185493, d186840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185499 q = 0) : d186846 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185499, d186846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185499, d186846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185508 q = 0) : d186855 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d185508, d186855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185508, d186855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185509 q = 0) : d186856 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d185509, d186856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185509, d186856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16957 (p : Pattern) (selected : d185515 p = 0) : d186862 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185502 q = 0) : d186849 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185502, d186849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16954 q selected
    | true =>
      simp only [d185502, d186849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185503 q = 0) : d186850 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185503, d186850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185503, d186850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185510 q = 0) : d186857 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185510, d186857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16956 q selected
    | true =>
      simp only [d185510, d186857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185511 q = 0) : d186858 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185511, d186858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185511, d186858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185512 q = 0) : d186859 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185512, d186859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185512, d186859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185513 q = 0) : d186860 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185513, d186860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185513, d186860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185514 q = 0) : d186861 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185514, d186861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185514, d186861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185515 q = 0) : d186862 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185515, d186862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185515, d186862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16958 (p : Pattern) (selected : d185517 p = 0) : d186825 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d16706 q = 0) : d127457 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16706, d127457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16706, d127457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6690 q selected
  have h2 (q : Pattern) (selected : d9896 q = 0) : d101310 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9896, d101310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6690 q selected
    | true =>
      simp only [d9896, d101310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d16707 q = 0) : d127458 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16707, d127458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d16707, d127458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9898 q = 0) : d101312 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9898, d101312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9898, d101312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d16708 q = 0) : d127459 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16708, d127459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d16708, d127459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15064 q = 0) : d123129 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15064, d123129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15064, d123129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6692 q selected
  have h7 (q : Pattern) (selected : d9918 q = 0) : d101321 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9918, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6692 q selected
    | true =>
      simp only [d9918, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15065 q = 0) : d123130 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15065, d123130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15065, d123130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d9920 q = 0) : d101323 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9920, d101323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d9920, d101323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15066 q = 0) : d123131 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15066, d123131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d15066, d123131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d185517 q = 0) : d186825 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185517, d186825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185517, d186825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16959 (p : Pattern) (selected : d185518 p = 0) : d186834 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1447 q = 0) : d52879 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1447, d52879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1447, d52879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro417 q selected
  have h2 (q : Pattern) (selected : d1276 q = 0) : d52702 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1276, d52702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro417 q selected
    | true =>
      simp only [d1276, d52702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1448 q = 0) : d52880 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1448, d52880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1448, d52880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1277 q = 0) : d52703 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1277, d52703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1277, d52703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1449 q = 0) : d52881 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1449, d52881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1449, d52881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185518 q = 0) : d186834 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185518, d186834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185518, d186834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16960 (p : Pattern) (selected : d185528 p = 0) : d186848 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185519 q = 0) : d186835 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185519, d186835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16958 q selected
    | true =>
      simp only [d185519, d186835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16959 q selected
  have h2 (q : Pattern) (selected : d185520 q = 0) : d186836 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185520, d186836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185520, d186836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185521 q = 0) : d186837 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185521, d186837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185521, d186837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185522 q = 0) : d186838 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185522, d186838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16959 q selected
    | true =>
      simp only [d185522, d186838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185523 q = 0) : d186839 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185523, d186839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185523, d186839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185524 q = 0) : d186840 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185524, d186840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185524, d186840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185525 q = 0) : d186841 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185525, d186841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185525, d186841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185526 q = 0) : d186846 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185526, d186846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185526, d186846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d185527 q = 0) : d186847 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d185527, d186847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185527, d186847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d185528 q = 0) : d186848 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d185528, d186848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d185528, d186848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16961 (p : Pattern) (selected : d185532 p = 0) : d186856 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185522 q = 0) : d186838 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185522, d186838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16959 q selected
    | true =>
      simp only [d185522, d186838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185523 q = 0) : d186839 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185523, d186839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185523, d186839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185524 q = 0) : d186840 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185524, d186840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185524, d186840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185526 q = 0) : d186846 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185526, d186846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185526, d186846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185531 q = 0) : d186855 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d185531, d186855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185531, d186855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185532 q = 0) : d186856 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d185532, d186856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185532, d186856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16962 (p : Pattern) (selected : d185538 p = 0) : d186862 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185529 q = 0) : d186849 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185529, d186849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16960 q selected
    | true =>
      simp only [d185529, d186849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185530 q = 0) : d186850 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185530, d186850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185530, d186850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185533 q = 0) : d186857 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185533, d186857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16961 q selected
    | true =>
      simp only [d185533, d186857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185534 q = 0) : d186858 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185534, d186858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185534, d186858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185535 q = 0) : d186859 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185535, d186859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185535, d186859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185536 q = 0) : d186860 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185536, d186860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185536, d186860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185537 q = 0) : d186861 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185537, d186861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185537, d186861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185538 q = 0) : d186862 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185538, d186862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185538, d186862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16963 (p : Pattern) (selected : d185542 p = 0) : d186867 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185533 q = 0) : d186857 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185533, d186857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16961 q selected
    | true =>
      simp only [d185533, d186857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185534 q = 0) : d186858 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185534, d186858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185534, d186858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185539 q = 0) : d186864 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185539, d186864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185539, d186864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185540 q = 0) : d186865 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185540, d186865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185540, d186865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185541 q = 0) : d186866 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185541, d186866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185541, d186866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185542 q = 0) : d186867 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185542, d186867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185542, d186867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16964 (p : Pattern) (selected : d185548 p = 0) : d186873 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185502 q = 0) : d186849 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185502, d186849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16954 q selected
    | true =>
      simp only [d185502, d186849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185503 q = 0) : d186850 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185503, d186850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185503, d186850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185545 q = 0) : d186870 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185545, d186870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185545, d186870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185546 q = 0) : d186871 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185546, d186871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185546, d186871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185547 q = 0) : d186872 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185547, d186872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185547, d186872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185548 q = 0) : d186873 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185548, d186873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185548, d186873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16965 (p : Pattern) (selected : d185554 p = 0) : d186879 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185516 q = 0) : d186863 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185516, d186863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16955 q selected
    | true =>
      simp only [d185516, d186863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16957 q selected
  have h2 (q : Pattern) (selected : d185543 q = 0) : d186868 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185543, d186868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16962 q selected
    | true =>
      simp only [d185543, d186868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16963 q selected
  have h3 (q : Pattern) (selected : d185544 q = 0) : d186869 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185544, d186869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d185544, d186869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185549 q = 0) : d186874 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185549, d186874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16964 q selected
    | true =>
      simp only [d185549, d186874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185550 q = 0) : d186875 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185550, d186875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185550, d186875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185551 q = 0) : d186876 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185551, d186876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185551, d186876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185552 q = 0) : d186877 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185552, d186877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185552, d186877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185553 q = 0) : d186878 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185553, d186878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185553, d186878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d185554 q = 0) : d186879 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d185554, d186879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185554, d186879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro16966 (p : Pattern) (selected : d185559 p = 0) : d186867 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185510 q = 0) : d186857 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185510, d186857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16956 q selected
    | true =>
      simp only [d185510, d186857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185511 q = 0) : d186858 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185511, d186858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185511, d186858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185556 q = 0) : d186864 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185556, d186864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185556, d186864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185557 q = 0) : d186865 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185557, d186865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185557, d186865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185558 q = 0) : d186866 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185558, d186866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185558, d186866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185559 q = 0) : d186867 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185559, d186867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185559, d186867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16967 (p : Pattern) (selected : d185565 p = 0) : d186886 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185560 q = 0) : d186881 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185560, d186881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16966 q selected
    | true =>
      simp only [d185560, d186881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185561 q = 0) : d186882 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185561, d186882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185561, d186882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185562 q = 0) : d186883 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185562, d186883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185562, d186883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185563 q = 0) : d186884 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185563, d186884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185563, d186884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185564 q = 0) : d186885 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185564, d186885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185564, d186885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185565 q = 0) : d186886 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d185565, d186886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185565, d186886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16968 (p : Pattern) (selected : d185571 p = 0) : d186892 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185340 q = 0) : d186717 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d185340, d186717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185340, d186717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16916 q selected
  have h2 (q : Pattern) (selected : d185341 q = 0) : d186718 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d185341, d186718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d185341, d186718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d185350 q = 0) : d186727 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d185350, d186727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16916 q selected
    | true =>
      simp only [d185350, d186727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16919 q selected
  have h4 (q : Pattern) (selected : d185351 q = 0) : d186728 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d185351, d186728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185351, d186728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185352 q = 0) : d186729 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d185352, d186729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185352, d186729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185450 q = 0) : d186797 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d185450, d186797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16935 q selected
    | true =>
      simp only [d185450, d186797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16944 q selected
  have h7 (q : Pattern) (selected : d185463 q = 0) : d186810 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d185463, d186810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16945 q selected
    | true =>
      simp only [d185463, d186810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16946 q selected
  have h8 (q : Pattern) (selected : d185464 q = 0) : d186811 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d185464, d186811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185464, d186811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d185465 q = 0) : d186812 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d185465, d186812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d185465, d186812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d185466 q = 0) : d186813 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d185466, d186813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185466, d186813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d185470 q = 0) : d186817 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d185470, d186817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185470, d186817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16947 q selected
  have h12 (q : Pattern) (selected : d185472 q = 0) : d186819 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d185472, d186819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185472, d186819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16948 q selected
  have h13 (q : Pattern) (selected : d185473 q = 0) : d186820 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d185473, d186820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d185473, d186820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d185474 q = 0) : d186821 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d185474, d186821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d185474, d186821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d185475 q = 0) : d186822 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d185475, d186822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d185475, d186822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d185476 q = 0) : d186823 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d185476, d186823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d185476, d186823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d185555 q = 0) : d186880 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d185555, d186880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185555, d186880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16965 q selected
  have h18 (q : Pattern) (selected : d185566 q = 0) : d186887 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d185566, d186887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185566, d186887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16967 q selected
  have h19 (q : Pattern) (selected : d185567 q = 0) : d186888 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d185567, d186888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d185567, d186888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d185568 q = 0) : d186889 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d185568, d186889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d185568, d186889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d185569 q = 0) : d186890 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d185569, d186890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d185569, d186890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d185570 q = 0) : d186891 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d185570, d186891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d185570, d186891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d185571 q = 0) : d186892 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d185571, d186892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d185571, d186892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro16969 (p : Pattern) (selected : d185577 p = 0) : d186898 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185572 q = 0) : d186893 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d185572, d186893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185572, d186893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16968 q selected
  have h2 (q : Pattern) (selected : d185573 q = 0) : d186894 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d185573, d186894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185573, d186894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185574 q = 0) : d186895 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d185574, d186895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185574, d186895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185575 q = 0) : d186896 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d185575, d186896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185575, d186896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185576 q = 0) : d186897 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d185576, d186897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185576, d186897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185577 q = 0) : d186898 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d185577, d186898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185577, d186898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16970 (p : Pattern) (selected : d185581 p = 0) : d186902 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10074 q = 0) : d101501 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10074, d101501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6716 q selected
    | true =>
      simp only [d10074, d101501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10076 q = 0) : d101503 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10076, d101503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10076, d101503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d16787 q = 0) : d127561 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16787, d127561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16787, d127561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10085 q = 0) : d101512 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6717 q selected
    | true =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10087 q = 0) : d101514 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10087, d101514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10087, d101514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d15156 q = 0) : d123241 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15156, d123241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15156, d123241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185581 q = 0) : d186902 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185581, d186902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185581, d186902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16971 (p : Pattern) (selected : d185582 p = 0) : d186903 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10115 q = 0) : d101542 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10115, d101542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6721 q selected
    | true =>
      simp only [d10115, d101542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10117 q = 0) : d101544 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10117, d101544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10117, d101544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d16792 q = 0) : d127566 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16792, d127566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16792, d127566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185582 q = 0) : d186903 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185582, d186903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185582, d186903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16972 (p : Pattern) (selected : d185592 p = 0) : d186913 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185583 q = 0) : d186904 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185583, d186904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16970 q selected
    | true =>
      simp only [d185583, d186904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16971 q selected
  have h2 (q : Pattern) (selected : d185584 q = 0) : d186905 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185584, d186905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185584, d186905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185585 q = 0) : d186906 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185585, d186906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185585, d186906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185586 q = 0) : d186907 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185586, d186907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16971 q selected
    | true =>
      simp only [d185586, d186907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185587 q = 0) : d186908 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185587, d186908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185587, d186908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185588 q = 0) : d186909 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185588, d186909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185588, d186909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185589 q = 0) : d186910 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185589, d186910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185589, d186910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185590 q = 0) : d186911 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185590, d186911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185590, d186911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d185591 q = 0) : d186912 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d185591, d186912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185591, d186912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d185592 q = 0) : d186913 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d185592, d186913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d185592, d186913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16973 (p : Pattern) (selected : d185596 p = 0) : d186917 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185586 q = 0) : d186907 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185586, d186907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16971 q selected
    | true =>
      simp only [d185586, d186907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185587 q = 0) : d186908 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185587, d186908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185587, d186908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185588 q = 0) : d186909 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185588, d186909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185588, d186909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185590 q = 0) : d186911 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185590, d186911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185590, d186911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185595 q = 0) : d186916 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d185595, d186916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185595, d186916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185596 q = 0) : d186917 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d185596, d186917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185596, d186917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16974 (p : Pattern) (selected : d185602 p = 0) : d186923 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185593 q = 0) : d186914 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185593, d186914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16972 q selected
    | true =>
      simp only [d185593, d186914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185594 q = 0) : d186915 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185594, d186915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185594, d186915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185597 q = 0) : d186918 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185597, d186918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16973 q selected
    | true =>
      simp only [d185597, d186918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185598 q = 0) : d186919 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185598, d186919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185598, d186919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185599 q = 0) : d186920 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185599, d186920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185599, d186920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185600 q = 0) : d186921 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185600, d186921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185600, d186921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185601 q = 0) : d186922 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185601, d186922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185601, d186922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185602 q = 0) : d186923 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185602, d186923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185602, d186923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16975 (p : Pattern) (selected : d185606 p = 0) : d186927 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185597 q = 0) : d186918 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185597, d186918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16973 q selected
    | true =>
      simp only [d185597, d186918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185598 q = 0) : d186919 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185598, d186919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185598, d186919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185603 q = 0) : d186924 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185603, d186924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185603, d186924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185604 q = 0) : d186925 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185604, d186925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185604, d186925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185605 q = 0) : d186926 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185605, d186926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185605, d186926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185606 q = 0) : d186927 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185606, d186927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185606, d186927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16976 (p : Pattern) (selected : d185612 p = 0) : d186933 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185607 q = 0) : d186928 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185607, d186928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16974 q selected
    | true =>
      simp only [d185607, d186928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16975 q selected
  have h2 (q : Pattern) (selected : d185608 q = 0) : d186929 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185608, d186929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185608, d186929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185609 q = 0) : d186930 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185609, d186930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185609, d186930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185610 q = 0) : d186931 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185610, d186931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185610, d186931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185611 q = 0) : d186932 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185611, d186932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185611, d186932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185612 q = 0) : d186933 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d185612, d186933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185612, d186933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16977 (p : Pattern) (selected : d185615 p = 0) : d186936 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185593 q = 0) : d186914 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185593, d186914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16972 q selected
    | true =>
      simp only [d185593, d186914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185594 q = 0) : d186915 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185594, d186915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185594, d186915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185597 q = 0) : d186918 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185597, d186918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16973 q selected
    | true =>
      simp only [d185597, d186918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185598 q = 0) : d186919 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185598, d186919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185598, d186919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185599 q = 0) : d186920 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185599, d186920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185599, d186920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185600 q = 0) : d186921 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185600, d186921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185600, d186921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185601 q = 0) : d186922 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185601, d186922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185601, d186922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185615 q = 0) : d186936 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185615, d186936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185615, d186936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16978 (p : Pattern) (selected : d185616 p = 0) : d186937 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185597 q = 0) : d186918 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185597, d186918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16973 q selected
    | true =>
      simp only [d185597, d186918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185598 q = 0) : d186919 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185598, d186919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185598, d186919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185603 q = 0) : d186924 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185603, d186924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185603, d186924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185604 q = 0) : d186925 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185604, d186925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185604, d186925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185605 q = 0) : d186926 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185605, d186926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185605, d186926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185616 q = 0) : d186937 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185616, d186937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185616, d186937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16979 (p : Pattern) (selected : d185622 p = 0) : d186943 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185607 q = 0) : d186928 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185607, d186928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16974 q selected
    | true =>
      simp only [d185607, d186928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16975 q selected
  have h2 (q : Pattern) (selected : d185608 q = 0) : d186929 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185608, d186929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185608, d186929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185609 q = 0) : d186930 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185609, d186930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185609, d186930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185610 q = 0) : d186931 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185610, d186931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185610, d186931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185611 q = 0) : d186932 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185611, d186932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185611, d186932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185617 q = 0) : d186938 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185617, d186938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16977 q selected
    | true =>
      simp only [d185617, d186938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16978 q selected
  have h7 (q : Pattern) (selected : d185618 q = 0) : d186939 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185618, d186939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185618, d186939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185619 q = 0) : d186940 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185619, d186940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185619, d186940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d185620 q = 0) : d186941 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185620, d186941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185620, d186941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d185621 q = 0) : d186942 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185621, d186942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185621, d186942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d185622 q = 0) : d186943 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d185622, d186943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185622, d186943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16980 (p : Pattern) (selected : d185627 p = 0) : d186948 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185593 q = 0) : d186914 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185593, d186914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16972 q selected
    | true =>
      simp only [d185593, d186914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185594 q = 0) : d186915 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185594, d186915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185594, d186915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185597 q = 0) : d186918 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185597, d186918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16973 q selected
    | true =>
      simp only [d185597, d186918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185598 q = 0) : d186919 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185598, d186919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185598, d186919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185599 q = 0) : d186920 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185599, d186920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185599, d186920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185600 q = 0) : d186921 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185600, d186921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185600, d186921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185626 q = 0) : d186947 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185626, d186947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185626, d186947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185627 q = 0) : d186948 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185627, d186948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185627, d186948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16981 (p : Pattern) (selected : d185629 p = 0) : d186950 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185597 q = 0) : d186918 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185597, d186918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16973 q selected
    | true =>
      simp only [d185597, d186918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185598 q = 0) : d186919 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185598, d186919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185598, d186919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185603 q = 0) : d186924 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185603, d186924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185603, d186924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185604 q = 0) : d186925 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185604, d186925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185604, d186925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185628 q = 0) : d186949 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185628, d186949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185628, d186949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185629 q = 0) : d186950 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185629, d186950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185629, d186950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16982 (p : Pattern) (selected : d185636 p = 0) : d186957 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185593 q = 0) : d186914 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185593, d186914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16972 q selected
    | true =>
      simp only [d185593, d186914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185594 q = 0) : d186915 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185594, d186915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185594, d186915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185597 q = 0) : d186918 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185597, d186918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16973 q selected
    | true =>
      simp only [d185597, d186918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185598 q = 0) : d186919 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185598, d186919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185598, d186919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185599 q = 0) : d186920 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185599, d186920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185599, d186920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185634 q = 0) : d186955 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185634, d186955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185634, d186955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185635 q = 0) : d186956 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185635, d186956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185635, d186956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185636 q = 0) : d186957 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185636, d186957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185636, d186957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16983 (p : Pattern) (selected : d185639 p = 0) : d186960 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185597 q = 0) : d186918 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185597, d186918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16973 q selected
    | true =>
      simp only [d185597, d186918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185598 q = 0) : d186919 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185598, d186919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185598, d186919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185603 q = 0) : d186924 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185603, d186924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185603, d186924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185637 q = 0) : d186958 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185637, d186958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185637, d186958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185638 q = 0) : d186959 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185638, d186959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185638, d186959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185639 q = 0) : d186960 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185639, d186960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185639, d186960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16984 (p : Pattern) (selected : d185643 p = 0) : d186964 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10036 q = 0) : d101463 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10036, d101463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6711 q selected
    | true =>
      simp only [d10036, d101463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10038 q = 0) : d101465 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10038, d101465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10038, d101465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d16859 q = 0) : d127633 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16859, d127633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16859, d127633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10063 q = 0) : d101490 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10063, d101490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6714 q selected
    | true =>
      simp only [d10063, d101490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10065 q = 0) : d101492 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10065, d101492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10065, d101492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d15151 q = 0) : d123236 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15151, d123236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15151, d123236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185643 q = 0) : d186964 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185643, d186964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185643, d186964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16985 (p : Pattern) (selected : d185647 p = 0) : d186968 p = 1 := by
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
  have h4 (q : Pattern) (selected : d185647 q = 0) : d186968 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185647, d186968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185647, d186968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16986 (p : Pattern) (selected : d185653 p = 0) : d186974 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185644 q = 0) : d186965 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185644, d186965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16984 q selected
    | true =>
      simp only [d185644, d186965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16970 q selected
  have h2 (q : Pattern) (selected : d185645 q = 0) : d186966 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185645, d186966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185645, d186966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185646 q = 0) : d186967 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185646, d186967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185646, d186967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185648 q = 0) : d186969 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185648, d186969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16970 q selected
    | true =>
      simp only [d185648, d186969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16985 q selected
  have h5 (q : Pattern) (selected : d185649 q = 0) : d186970 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185649, d186970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185649, d186970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185650 q = 0) : d186971 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185650, d186971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185650, d186971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185651 q = 0) : d186972 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185651, d186972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185651, d186972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185583 q = 0) : d186904 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185583, d186904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16970 q selected
    | true =>
      simp only [d185583, d186904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16971 q selected
  have h9 (q : Pattern) (selected : d185584 q = 0) : d186905 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185584, d186905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185584, d186905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d185585 q = 0) : d186906 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185585, d186906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185585, d186906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d185586 q = 0) : d186907 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185586, d186907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16971 q selected
    | true =>
      simp only [d185586, d186907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d185587 q = 0) : d186908 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185587, d186908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185587, d186908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d185588 q = 0) : d186909 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185588, d186909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185588, d186909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d185589 q = 0) : d186910 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185589, d186910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d185589, d186910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d185652 q = 0) : d186973 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d185652, d186973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185652, d186973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d185653 q = 0) : d186974 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d185653, d186974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d185653, d186974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro16987 (p : Pattern) (selected : d185659 p = 0) : d186980 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185654 q = 0) : d186975 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185654, d186975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16986 q selected
    | true =>
      simp only [d185654, d186975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185655 q = 0) : d186976 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185655, d186976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185655, d186976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185593 q = 0) : d186914 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185593, d186914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16972 q selected
    | true =>
      simp only [d185593, d186914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185594 q = 0) : d186915 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185594, d186915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185594, d186915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185656 q = 0) : d186977 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185656, d186977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185656, d186977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185657 q = 0) : d186978 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185657, d186978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185657, d186978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185658 q = 0) : d186979 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185658, d186979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185658, d186979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185659 q = 0) : d186980 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185659, d186980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185659, d186980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16988 (p : Pattern) (selected : d185661 p = 0) : d186902 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10190 q = 0) : d101501 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10190, d101501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6733 q selected
    | true =>
      simp only [d10190, d101501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10192 q = 0) : d101503 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10192, d101503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10192, d101503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d16891 q = 0) : d127561 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16891, d127561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16891, d127561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10215 q = 0) : d101512 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10215, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6735 q selected
    | true =>
      simp only [d10215, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10217 q = 0) : d101514 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10217, d101514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10217, d101514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d15266 q = 0) : d123241 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15266, d123241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15266, d123241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185661 q = 0) : d186902 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185661, d186902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185661, d186902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16989 (p : Pattern) (selected : d185662 p = 0) : d186903 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10226 q = 0) : d101542 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10226, d101542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6737 q selected
    | true =>
      simp only [d10226, d101542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10228 q = 0) : d101544 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10228, d101544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10228, d101544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d16896 q = 0) : d127566 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16896, d127566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16896, d127566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185662 q = 0) : d186903 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185662, d186903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185662, d186903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16990 (p : Pattern) (selected : d185672 p = 0) : d186913 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185663 q = 0) : d186904 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185663, d186904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16988 q selected
    | true =>
      simp only [d185663, d186904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16989 q selected
  have h2 (q : Pattern) (selected : d185664 q = 0) : d186905 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185664, d186905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185664, d186905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185665 q = 0) : d186906 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185665, d186906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185665, d186906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185666 q = 0) : d186907 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185666, d186907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16989 q selected
    | true =>
      simp only [d185666, d186907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185667 q = 0) : d186908 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185667, d186908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185667, d186908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185668 q = 0) : d186909 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185668, d186909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185668, d186909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185669 q = 0) : d186910 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185669, d186910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185669, d186910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185670 q = 0) : d186911 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185670, d186911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185670, d186911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d185671 q = 0) : d186912 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d185671, d186912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185671, d186912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d185672 q = 0) : d186913 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d185672, d186913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d185672, d186913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16991 (p : Pattern) (selected : d185676 p = 0) : d186917 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185666 q = 0) : d186907 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185666, d186907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16989 q selected
    | true =>
      simp only [d185666, d186907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185667 q = 0) : d186908 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185667, d186908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185667, d186908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185668 q = 0) : d186909 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185668, d186909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185668, d186909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185670 q = 0) : d186911 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185670, d186911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185670, d186911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185675 q = 0) : d186916 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d185675, d186916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185675, d186916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185676 q = 0) : d186917 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d185676, d186917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185676, d186917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16992 (p : Pattern) (selected : d185682 p = 0) : d186923 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185673 q = 0) : d186914 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185673, d186914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16990 q selected
    | true =>
      simp only [d185673, d186914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185674 q = 0) : d186915 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185674, d186915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185674, d186915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185677 q = 0) : d186918 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185677, d186918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16991 q selected
    | true =>
      simp only [d185677, d186918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185678 q = 0) : d186919 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185678, d186919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185678, d186919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185679 q = 0) : d186920 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185679, d186920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185679, d186920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185680 q = 0) : d186921 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185680, d186921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185680, d186921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185681 q = 0) : d186922 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185681, d186922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185681, d186922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185682 q = 0) : d186923 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185682, d186923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185682, d186923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16993 (p : Pattern) (selected : d185686 p = 0) : d186927 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185677 q = 0) : d186918 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185677, d186918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16991 q selected
    | true =>
      simp only [d185677, d186918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185678 q = 0) : d186919 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185678, d186919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185678, d186919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185683 q = 0) : d186924 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185683, d186924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185683, d186924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185684 q = 0) : d186925 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185684, d186925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185684, d186925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185685 q = 0) : d186926 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185685, d186926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185685, d186926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185686 q = 0) : d186927 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185686, d186927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185686, d186927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16994 (p : Pattern) (selected : d185692 p = 0) : d186986 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185593 q = 0) : d186914 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185593, d186914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16972 q selected
    | true =>
      simp only [d185593, d186914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185594 q = 0) : d186915 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185594, d186915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185594, d186915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185689 q = 0) : d186983 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185689, d186983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185689, d186983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185690 q = 0) : d186984 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185690, d186984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185690, d186984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185691 q = 0) : d186985 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185691, d186985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185691, d186985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185692 q = 0) : d186986 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185692, d186986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185692, d186986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16995 (p : Pattern) (selected : d185698 p = 0) : d186992 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185630 q = 0) : d186951 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185630, d186951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16980 q selected
    | true =>
      simp only [d185630, d186951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16981 q selected
  have h2 (q : Pattern) (selected : d185631 q = 0) : d186952 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185631, d186952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185631, d186952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185632 q = 0) : d186953 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185632, d186953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185632, d186953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185633 q = 0) : d186954 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185633, d186954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185633, d186954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185640 q = 0) : d186961 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185640, d186961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16982 q selected
    | true =>
      simp only [d185640, d186961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16983 q selected
  have h6 (q : Pattern) (selected : d185641 q = 0) : d186962 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185641, d186962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185641, d186962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185642 q = 0) : d186963 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185642, d186963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185642, d186963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185660 q = 0) : d186981 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185660, d186981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16987 q selected
    | true =>
      simp only [d185660, d186981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16974 q selected
  have h9 (q : Pattern) (selected : d185687 q = 0) : d186928 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185687, d186928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16992 q selected
    | true =>
      simp only [d185687, d186928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16993 q selected
  have h10 (q : Pattern) (selected : d185688 q = 0) : d186982 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185688, d186982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d185688, d186982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d185693 q = 0) : d186987 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185693, d186987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16994 q selected
    | true =>
      simp only [d185693, d186987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d185694 q = 0) : d186988 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185694, d186988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d185694, d186988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d185695 q = 0) : d186989 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185695, d186989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d185695, d186989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d185696 q = 0) : d186990 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185696, d186990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185696, d186990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d185697 q = 0) : d186991 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185697, d186991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185697, d186991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d185698 q = 0) : d186992 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d185698, d186992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185698, d186992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro16996 (p : Pattern) (selected : d185699 p = 0) : d186993 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185593 q = 0) : d186914 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185593, d186914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16972 q selected
    | true =>
      simp only [d185593, d186914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185594 q = 0) : d186915 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185594, d186915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185594, d186915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185597 q = 0) : d186918 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185597, d186918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16973 q selected
    | true =>
      simp only [d185597, d186918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185598 q = 0) : d186919 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185598, d186919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185598, d186919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185599 q = 0) : d186920 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185599, d186920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185599, d186920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185600 q = 0) : d186921 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185600, d186921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185600, d186921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185626 q = 0) : d186947 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185626, d186947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185626, d186947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185699 q = 0) : d186993 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185699, d186993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185699, d186993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16997 (p : Pattern) (selected : d185700 p = 0) : d186994 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185597 q = 0) : d186918 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185597, d186918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16973 q selected
    | true =>
      simp only [d185597, d186918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185598 q = 0) : d186919 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185598, d186919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185598, d186919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185603 q = 0) : d186924 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185603, d186924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185603, d186924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185604 q = 0) : d186925 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185604, d186925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185604, d186925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185628 q = 0) : d186949 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185628, d186949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185628, d186949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185700 q = 0) : d186994 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185700, d186994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185700, d186994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16998 (p : Pattern) (selected : d185705 p = 0) : d186999 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185593 q = 0) : d186914 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185593, d186914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16972 q selected
    | true =>
      simp only [d185593, d186914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185594 q = 0) : d186915 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185594, d186915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185594, d186915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185597 q = 0) : d186918 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185597, d186918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16973 q selected
    | true =>
      simp only [d185597, d186918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185598 q = 0) : d186919 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185598, d186919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185598, d186919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185599 q = 0) : d186920 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185599, d186920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185599, d186920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185634 q = 0) : d186955 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185634, d186955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185634, d186955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185635 q = 0) : d186956 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185635, d186956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185635, d186956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185705 q = 0) : d186999 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185705, d186999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185705, d186999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16999 (p : Pattern) (selected : d185706 p = 0) : d187000 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185597 q = 0) : d186918 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185597, d186918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16973 q selected
    | true =>
      simp only [d185597, d186918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185598 q = 0) : d186919 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185598, d186919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185598, d186919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185603 q = 0) : d186924 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185603, d186924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185603, d186924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185637 q = 0) : d186958 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185637, d186958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185637, d186958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185638 q = 0) : d186959 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185638, d186959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185638, d186959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185706 q = 0) : d187000 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185706, d187000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185706, d187000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
end NetHack.Soko22Hazard87
