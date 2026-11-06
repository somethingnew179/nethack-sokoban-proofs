import NetHack.Soko22Hazard87.AndIntroBlocks0040
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro10250 (p : Pattern) (ha : d85329 p = 1) (hb : d85659 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8154 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d85324 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85325 q = 1) (hb : d85655 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85325, d85655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85325, d85655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d8170 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85326 q = 1) (hb : d85656 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85326, d85656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85326, d85656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85327 q = 1) (hb : d85657 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85327, d85657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85327, d85657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85328 q = 1) (hb : d85658 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85328, d85658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85328, d85658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85329 q = 1) (hb : d85659 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85329, d85659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85329, d85659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10251 (p : Pattern) (ha : d85335 p = 1) (hb : d85665 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d8061 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85052 q = 1) (hb : d85643 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85052, d85643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10247 q ha hb
    | true =>
      simp only [d85052, d85643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10248 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8126 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85053 q = 1) (hb : d85644 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85053, d85644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85053, d85644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85316 q = 1) (hb : d85645 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85316, d85645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85316, d85645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85317 q = 1) (hb : d85646 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85317, d85646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85317, d85646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85319 q = 1) (hb : d85650 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85319, d85650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85319, d85650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10249 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d2326 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d85320 q = 1) (hb : d85651 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85320, d85651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d85320, d85651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85321 q = 1) (hb : d85652 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85321, d85652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85321, d85652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d85322 q = 1) (hb : d85653 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85322, d85653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85322, d85653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d85323 q = 1) (hb : d85654 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85323, d85654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85323, d85654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85330 q = 1) (hb : d85660 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85330, d85660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85330, d85660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10250 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d2459 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d85331 q = 1) (hb : d85661 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85331, d85661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85331, d85661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d85332 q = 1) (hb : d85662 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85332, d85662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85332, d85662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d85333 q = 1) (hb : d85663 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85333, d85663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d85333, d85663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d85334 q = 1) (hb : d85664 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85334, d85664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85334, d85664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d85335 q = 1) (hb : d85665 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85335, d85665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85335, d85665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro10252 (p : Pattern) (ha : d85341 p = 1) (hb : d85671 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85336 q = 1) (hb : d85666 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85336, d85666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85336, d85666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10251 q ha hb
  have h2 (q : Pattern) (ha : d85337 q = 1) (hb : d85667 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85337, d85667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85337, d85667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85338 q = 1) (hb : d85668 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85338, d85668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85338, d85668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85339 q = 1) (hb : d85669 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85339, d85669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85339, d85669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85340 q = 1) (hb : d85670 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85340, d85670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85340, d85670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85341 q = 1) (hb : d85671 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85341, d85671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85341, d85671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10253 (p : Pattern) (ha : d85347 p = 1) (hb : d85677 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d85228 q = 1) (hb : d85506 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d85228, d85506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10222 q ha hb
    | true =>
      simp only [d85228, d85506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10228 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d85255 q = 1) (hb : d85546 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d85255, d85546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85255, d85546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10234 q ha hb
  have h3 (q : Pattern) (ha : d85256 q = 1) (hb : d85547 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d85256, d85547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85256, d85547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85283 q = 1) (hb : d85587 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d85283, d85587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85283, d85587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10240 q ha hb
  have h5 (q : Pattern) (ha : d85284 q = 1) (hb : d85588 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d85284, d85588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85284, d85588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85285 q = 1) (hb : d85589 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d85285, d85589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85285, d85589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85312 q = 1) (hb : d85629 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d85312, d85629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85312, d85629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10246 q ha hb
  have h8 (q : Pattern) (ha : d85313 q = 1) (hb : d85630 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d85313, d85630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85313, d85630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85314 q = 1) (hb : d85631 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d85314, d85631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85314, d85631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85315 q = 1) (hb : d85632 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d85315, d85632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85315, d85632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d85342 q = 1) (hb : d85672 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d85342, d85672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85342, d85672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10252 q ha hb
  have h12 (q : Pattern) (ha : d85343 q = 1) (hb : d85673 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d85343, d85673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85343, d85673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85344 q = 1) (hb : d85674 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d85344, d85674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85344, d85674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85345 q = 1) (hb : d85675 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d85345, d85675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85345, d85675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d85346 q = 1) (hb : d85676 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d85346, d85676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85346, d85676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d85347 q = 1) (hb : d85677 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d85347, d85677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85347, d85677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro10254 (p : Pattern) (ha : d85353 p = 1) (hb : d85683 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85348 q = 1) (hb : d85678 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d85348, d85678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10253 q ha hb
    | true =>
      simp only [d85348, d85678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85349 q = 1) (hb : d85679 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d85349, d85679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85349, d85679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85350 q = 1) (hb : d85680 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d85350, d85680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85350, d85680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85351 q = 1) (hb : d85681 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d85351, d85681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85351, d85681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85352 q = 1) (hb : d85682 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d85352, d85682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85352, d85682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85353 q = 1) (hb : d85683 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d85353, d85683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85353, d85683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro10255 (p : Pattern) (ha : d85359 p = 1) (hb : d85689 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85354 q = 1) (hb : d85684 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d85354, d85684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10254 q ha hb
    | true =>
      simp only [d85354, d85684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85355 q = 1) (hb : d85685 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d85355, d85685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85355, d85685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85356 q = 1) (hb : d85686 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d85356, d85686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85356, d85686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85357 q = 1) (hb : d85687 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d85357, d85687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85357, d85687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85358 q = 1) (hb : d85688 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d85358, d85688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85358, d85688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85359 q = 1) (hb : d85689 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d85359, d85689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85359, d85689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro10256 (p : Pattern) (ha : d85365 p = 1) (hb : d85695 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85360 q = 1) (hb : d85690 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d85360, d85690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10255 q ha hb
    | true =>
      simp only [d85360, d85690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85361 q = 1) (hb : d85691 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d85361, d85691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85361, d85691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85362 q = 1) (hb : d85692 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d85362, d85692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85362, d85692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85363 q = 1) (hb : d85693 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d85363, d85693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85363, d85693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85364 q = 1) (hb : d85694 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d85364, d85694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85364, d85694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85365 q = 1) (hb : d85695 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d85365, d85695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85365, d85695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro10257 (p : Pattern) (ha : d85371 p = 1) (hb : d85701 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85366 q = 1) (hb : d85696 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d85366, d85696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10256 q ha hb
    | true =>
      simp only [d85366, d85696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85367 q = 1) (hb : d85697 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d85367, d85697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85367, d85697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85368 q = 1) (hb : d85698 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d85368, d85698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85368, d85698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85369 q = 1) (hb : d85699 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d85369, d85699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85369, d85699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85370 q = 1) (hb : d85700 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d85370, d85700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85370, d85700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85371 q = 1) (hb : d85701 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d85371, d85701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85371, d85701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro10258 (p : Pattern) (ha : d85377 p = 1) (hb : d85707 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85372 q = 1) (hb : d85702 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d85372, d85702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10257 q ha hb
    | true =>
      simp only [d85372, d85702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85373 q = 1) (hb : d85703 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d85373, d85703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85373, d85703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85374 q = 1) (hb : d85704 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d85374, d85704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85374, d85704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85375 q = 1) (hb : d85705 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d85375, d85705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85375, d85705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85376 q = 1) (hb : d85706 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d85376, d85706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85376, d85706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85377 q = 1) (hb : d85707 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d85377, d85707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85377, d85707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro10259 (p : Pattern) (ha : d85383 p = 1) (hb : d85713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85378 q = 1) (hb : d85708 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d85378, d85708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10258 q ha hb
    | true =>
      simp only [d85378, d85708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85379 q = 1) (hb : d85709 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d85379, d85709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85379, d85709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85380 q = 1) (hb : d85710 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d85380, d85710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85380, d85710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85381 q = 1) (hb : d85711 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d85381, d85711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85381, d85711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85382 q = 1) (hb : d85712 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d85382, d85712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85382, d85712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85383 q = 1) (hb : d85713 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d85383, d85713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85383, d85713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro10260 (p : Pattern) (ha : d85389 p = 1) (hb : d85719 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85384 q = 1) (hb : d85714 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d85384, d85714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10259 q ha hb
    | true =>
      simp only [d85384, d85714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85385 q = 1) (hb : d85715 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d85385, d85715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85385, d85715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85386 q = 1) (hb : d85716 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d85386, d85716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85386, d85716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85387 q = 1) (hb : d85717 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d85387, d85717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85387, d85717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85388 q = 1) (hb : d85718 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d85388, d85718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85388, d85718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85389 q = 1) (hb : d85719 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d85389, d85719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85389, d85719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro10261 (p : Pattern) (ha : d36 p = 1) (hb : d85723 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d34 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d35 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d35, d85723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d35, d85723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d36 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d36, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro10262 (p : Pattern) (ha : d42 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d37 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10261 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d39 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d41 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d42 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10263 (p : Pattern) (ha : d48 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10262 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d47 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d48 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
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
theorem andIntro10264 (p : Pattern) (ha : d49 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10261 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d39 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d40 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d41 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d49 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d49, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d49, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro10265 (p : Pattern) (ha : d55 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10262 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d47 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d50 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10264 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d51 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d52 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d55 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
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
theorem andIntro10266 (p : Pattern) (ha : d60 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d50 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10264 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d52 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d60 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
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
theorem andIntro10267 (p : Pattern) (ha : d77 p = 1) (hb : d85723 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d76 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d76, d85723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76, d85723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d77 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d77, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro10268 (p : Pattern) (ha : d83 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10267 q ha hb
    | true =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d79 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d80 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d81 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d81, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d81, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d82, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d83 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro10269 (p : Pattern) (ha : d89 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10268 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d86 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d86, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d87 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d87, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d88 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
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
theorem andIntro10270 (p : Pattern) (ha : d95 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10263 q ha hb
    | true =>
      simp only [d56, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10265 q ha hb
  have h2 (q : Pattern) (ha : d57 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d57, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d59 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d59, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10266 q ha hb
  have h6 (q : Pattern) (ha : d62 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d63 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d63, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d64 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d64, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d64, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d65 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d65, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d65, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d90 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d90, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10269 q ha hb
  have h11 (q : Pattern) (ha : d91 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d91, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d91, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d92 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d93 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d93, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d94 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d95 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
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
theorem andIntro10271 (p : Pattern) (ha : d104 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10262 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d100 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d104 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
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
theorem andIntro10272 (p : Pattern) (ha : d111 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10262 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d100 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d50 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10264 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d107 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d109 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d110 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d111 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
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
theorem andIntro10273 (p : Pattern) (ha : d213 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10262 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d100 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d213 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
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
theorem andIntro10274 (p : Pattern) (ha : d116 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d37 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10261 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d39 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d115 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d116 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10275 (p : Pattern) (ha : d123 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d37 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10261 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d39 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d121 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d123 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10276 (p : Pattern) (ha : d150 p = 1) (hb : d85723 p = 1) : d88140 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d148 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d34 q = 1) (hb : d85721 q = 1) : d34 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d149 q = 1) (hb : d85723 q = 1) : d88139 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d149, d85723, d88139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d149, d85723, d88139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d150 q = 1) (hb : d85723 q = 1) : d88140 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d150, d88140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150, d88140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro10277 (p : Pattern) (ha : d4736 p = 1) (hb : d85724 p = 1) : d88146 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d151 q = 1) (hb : d85723 q = 1) : d88141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10276 q ha hb
    | true =>
      simp only [d151, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d152 q = 1) (hb : d85723 q = 1) : d88142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d152, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4733 q = 1) (hb : d85724 q = 1) : d88143 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d85724, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4733, d85724, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4734 q = 1) (hb : d85724 q = 1) : d88144 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4734, d88144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4734, d88144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d4735 q = 1) (hb : d85724 q = 1) : d88145 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4735, d88145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4735, d88145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d4736 q = 1) (hb : d85724 q = 1) : d88146 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d4736, d88146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4736, d88146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10278 (p : Pattern) (ha : d76787 p = 1) (hb : d85724 p = 1) : d88152 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10274 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10275 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d5850 q = 1) (hb : d85724 q = 1) : d88147 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5850, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10277 q ha hb
    | true =>
      simp only [d5850, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10262 q ha hb
  have h9 (q : Pattern) (ha : d76783 q = 1) (hb : d85724 q = 1) : d88148 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76783, d88148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76783, d88148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10262 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d76784 q = 1) (hb : d85724 q = 1) : d88149 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76784, d88149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76784, d88149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d76785 q = 1) (hb : d85724 q = 1) : d88150 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76785, d88150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d76785, d88150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d76786 q = 1) (hb : d85724 q = 1) : d88151 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76786, d88151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76786, d88151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76787 q = 1) (hb : d85724 q = 1) : d88152 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76787, d88152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76787, d88152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro10279 (p : Pattern) (ha : d194 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d37 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10261 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d39 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d115 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d194 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro10280 (p : Pattern) (ha : d199 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d37 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10261 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d39 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d121 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d199 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro10281 (p : Pattern) (ha : d5355 p = 1) (hb : d85724 p = 1) : d88153 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d85723 q = 1) : d88141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10276 q ha hb
    | true =>
      simp only [d151, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d85723 q = 1) : d88142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4733 q = 1) (hb : d85724 q = 1) : d88143 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d85724, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4733, d85724, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d4734 q = 1) (hb : d85724 q = 1) : d88144 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4734, d88144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4734, d88144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4735 q = 1) (hb : d85724 q = 1) : d88145 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4735, d88145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4735, d88145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d5355 q = 1) (hb : d85724 q = 1) : d88153 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5355, d88153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5355, d88153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro10282 (p : Pattern) (ha : d76792 p = 1) (hb : d85724 p = 1) : d88159 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10274 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10275 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d5850 q = 1) (hb : d85724 q = 1) : d88147 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5850, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10277 q ha hb
    | true =>
      simp only [d5850, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10262 q ha hb
  have h9 (q : Pattern) (ha : d76783 q = 1) (hb : d85724 q = 1) : d88148 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76783, d88148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76783, d88148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10262 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d76784 q = 1) (hb : d85724 q = 1) : d88149 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76784, d88149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76784, d88149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d76785 q = 1) (hb : d85724 q = 1) : d88150 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76785, d88150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d76785, d88150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d76786 q = 1) (hb : d85724 q = 1) : d88151 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76786, d88151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76786, d88151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d195 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10279 q ha hb
    | true =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d196 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d197 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d198 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d200 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10280 q ha hb
    | true =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d201 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d202 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d5856 q = 1) (hb : d85724 q = 1) : d88154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5856, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10281 q ha hb
    | true =>
      simp only [d5856, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10264 q ha hb
  have h23 (q : Pattern) (ha : d76788 q = 1) (hb : d85724 q = 1) : d88155 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76788, d88155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d76788, d88155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d50 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10264 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d51 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d76789 q = 1) (hb : d85724 q = 1) : d88156 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76789, d88156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d76789, d88156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d76790 q = 1) (hb : d85724 q = 1) : d88157 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76790, d88157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d76790, d88157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d76791 q = 1) (hb : d85724 q = 1) : d88158 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76791, d88158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d76791, d88158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d76792 q = 1) (hb : d85724 q = 1) : d88159 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76792, d88159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d76792, d88159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro10283 (p : Pattern) (ha : d76799 p = 1) (hb : d85724 p = 1) : d88164 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5856 q = 1) (hb : d85724 q = 1) : d88154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5856, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10281 q ha hb
    | true =>
      simp only [d5856, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10264 q ha hb
  have h2 (q : Pattern) (ha : d76788 q = 1) (hb : d85724 q = 1) : d88155 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76788, d88155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76788, d88155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d50 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10264 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d76789 q = 1) (hb : d85724 q = 1) : d88156 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76789, d88156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76789, d88156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76797 q = 1) (hb : d85724 q = 1) : d88157 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76797, d88157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76797, d88157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76798 q = 1) (hb : d85724 q = 1) : d88158 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76798, d88158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76798, d88158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76799 q = 1) (hb : d85724 q = 1) : d88164 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76799, d88164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76799, d88164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10284 (p : Pattern) (ha : d237 p = 1) (hb : d85723 p = 1) : d88171 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d235 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75 q = 1) (hb : d85721 q = 1) : d75 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d236 q = 1) (hb : d85723 q = 1) : d88170 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d236, d85723, d88170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d236, d85723, d88170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d237 q = 1) (hb : d85723 q = 1) : d88171 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237, d88171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237, d88171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro10285 (p : Pattern) (ha : d5377 p = 1) (hb : d85724 p = 1) : d88177 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238 q = 1) (hb : d85723 q = 1) : d88172 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d88172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10284 q ha hb
    | true =>
      simp only [d238, d88172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239 q = 1) (hb : d85723 q = 1) : d88173 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d88173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d88173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5374 q = 1) (hb : d85724 q = 1) : d88174 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5374, d85724, d88174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5374, d85724, d88174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d5375 q = 1) (hb : d85724 q = 1) : d88175 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5375, d88175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5375, d88175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5376 q = 1) (hb : d85724 q = 1) : d88176 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5376, d88176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5376, d88176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d5377 q = 1) (hb : d85724 q = 1) : d88177 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5377, d88177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5377, d88177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro10286 (p : Pattern) (ha : d76809 p = 1) (hb : d85724 p = 1) : d88183 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5874 q = 1) (hb : d85724 q = 1) : d88178 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5874, d88178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10285 q ha hb
    | true =>
      simp only [d5874, d88178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10268 q ha hb
  have h2 (q : Pattern) (ha : d76805 q = 1) (hb : d85724 q = 1) : d88179 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76805, d88179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76805, d88179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d84 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10268 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d76806 q = 1) (hb : d85724 q = 1) : d88180 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76806, d88180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76806, d88180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76807 q = 1) (hb : d85724 q = 1) : d88181 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76807, d88181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76807, d88181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76808 q = 1) (hb : d85724 q = 1) : d88182 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76808, d88182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76808, d88182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76809 q = 1) (hb : d85724 q = 1) : d88183 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76809, d88183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76809, d88183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10287 (p : Pattern) (ha : d76815 p = 1) (hb : d85724 p = 1) : d88189 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10271 q ha hb
  have h2 (q : Pattern) (ha : d106 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10271 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10272 q ha hb
  have h4 (q : Pattern) (ha : d113 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d114 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76793 q = 1) (hb : d85724 q = 1) : d88160 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76793, d88160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10278 q ha hb
    | true =>
      simp only [d76793, d88160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10282 q ha hb
  have h7 (q : Pattern) (ha : d214 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10273 q ha hb
    | true =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d76794 q = 1) (hb : d85724 q = 1) : d88161 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76794, d88161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76794, d88161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76795 q = 1) (hb : d85724 q = 1) : d88162 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76795, d88162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76795, d88162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d76796 q = 1) (hb : d85724 q = 1) : d88163 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76796, d88163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76796, d88163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d76800 q = 1) (hb : d85724 q = 1) : d88165 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76800, d88165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76800, d88165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10283 q ha hb
  have h12 (q : Pattern) (ha : d76801 q = 1) (hb : d85724 q = 1) : d88166 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76801, d88166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76801, d88166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d76802 q = 1) (hb : d85724 q = 1) : d88167 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76802, d88167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d76802, d88167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d76803 q = 1) (hb : d85724 q = 1) : d88168 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76803, d88168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76803, d88168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d76804 q = 1) (hb : d85724 q = 1) : d88169 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76804, d88169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76804, d88169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d76810 q = 1) (hb : d85724 q = 1) : d88184 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76810, d88184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76810, d88184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10286 q ha hb
  have h17 (q : Pattern) (ha : d76811 q = 1) (hb : d85724 q = 1) : d88185 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76811, d88185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d76811, d88185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d76812 q = 1) (hb : d85724 q = 1) : d88186 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76812, d88186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d76812, d88186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d76813 q = 1) (hb : d85724 q = 1) : d88187 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76813, d88187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d76813, d88187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d76814 q = 1) (hb : d85724 q = 1) : d88188 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76814, d88188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d76814, d88188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d76815 q = 1) (hb : d85724 q = 1) : d88189 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d76815, d88189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d76815, d88189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro10288 (p : Pattern) (ha : d406 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d50 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10264 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d107 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d110 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d406 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
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
theorem andIntro10289 (p : Pattern) (ha : d462 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10268 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d458 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d459 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d460 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d461 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d462 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
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
theorem andIntro10290 (p : Pattern) (ha : d5895 p = 1) (hb : d85724 p = 1) : d88199 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5850 q = 1) (hb : d85724 q = 1) : d88147 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5850, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10277 q ha hb
    | true =>
      simp only [d5850, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10262 q ha hb
  have h2 (q : Pattern) (ha : d5891 q = 1) (hb : d85724 q = 1) : d88195 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5891, d88195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5891, d88195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5892 q = 1) (hb : d85724 q = 1) : d88196 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5892, d88196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5892, d88196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5893 q = 1) (hb : d85724 q = 1) : d88197 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5893, d88197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5893, d88197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5894 q = 1) (hb : d85724 q = 1) : d88198 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5894, d88198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5894, d88198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5895 q = 1) (hb : d85724 q = 1) : d88199 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d5895, d88199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5895, d88199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10291 (p : Pattern) (ha : d5902 p = 1) (hb : d85724 p = 1) : d88206 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5850 q = 1) (hb : d85724 q = 1) : d88147 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5850, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10277 q ha hb
    | true =>
      simp only [d5850, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10262 q ha hb
  have h2 (q : Pattern) (ha : d5891 q = 1) (hb : d85724 q = 1) : d88195 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5891, d88195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5891, d88195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5892 q = 1) (hb : d85724 q = 1) : d88196 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5892, d88196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5892, d88196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5893 q = 1) (hb : d85724 q = 1) : d88197 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5893, d88197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5893, d88197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5894 q = 1) (hb : d85724 q = 1) : d88198 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5894, d88198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5894, d88198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5856 q = 1) (hb : d85724 q = 1) : d88154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5856, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10281 q ha hb
    | true =>
      simp only [d5856, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10264 q ha hb
  have h7 (q : Pattern) (ha : d5898 q = 1) (hb : d85724 q = 1) : d88202 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5898, d88202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5898, d88202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5899 q = 1) (hb : d85724 q = 1) : d88203 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5899, d88203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5899, d88203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d5900 q = 1) (hb : d85724 q = 1) : d88204 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5900, d88204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5900, d88204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d5901 q = 1) (hb : d85724 q = 1) : d88205 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5901, d88205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5901, d88205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d5902 q = 1) (hb : d85724 q = 1) : d88206 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d5902, d88206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5902, d88206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro10292 (p : Pattern) (ha : d5952 p = 1) (hb : d85724 p = 1) : d88253 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5850 q = 1) (hb : d85724 q = 1) : d88147 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5850, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10277 q ha hb
    | true =>
      simp only [d5850, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10262 q ha hb
  have h2 (q : Pattern) (ha : d5891 q = 1) (hb : d85724 q = 1) : d88195 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5891, d88195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5891, d88195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5892 q = 1) (hb : d85724 q = 1) : d88196 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5892, d88196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5892, d88196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5893 q = 1) (hb : d85724 q = 1) : d88197 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5893, d88197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5893, d88197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5894 q = 1) (hb : d85724 q = 1) : d88198 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5894, d88198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5894, d88198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10262 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d100 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d102 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d103 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d5952 q = 1) (hb : d85724 q = 1) : d88253 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d5952, d88253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5952, d88253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro10293 (p : Pattern) (ha : d5907 p = 1) (hb : d85724 p = 1) : d88211 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d151 q = 1) (hb : d85723 q = 1) : d88141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10276 q ha hb
    | true =>
      simp only [d151, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d152 q = 1) (hb : d85723 q = 1) : d88142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d152, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4733 q = 1) (hb : d85724 q = 1) : d88143 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d85724, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4733, d85724, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4734 q = 1) (hb : d85724 q = 1) : d88144 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4734, d88144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4734, d88144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d5906 q = 1) (hb : d85724 q = 1) : d88210 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5906, d88210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5906, d88210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5907 q = 1) (hb : d85724 q = 1) : d88211 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5907, d88211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5907, d88211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10294 (p : Pattern) (ha : d5914 p = 1) (hb : d85724 p = 1) : d88218 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d151 q = 1) (hb : d85723 q = 1) : d88141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10276 q ha hb
    | true =>
      simp only [d151, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d152 q = 1) (hb : d85723 q = 1) : d88142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d152, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4733 q = 1) (hb : d85724 q = 1) : d88143 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d85724, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4733, d85724, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5912 q = 1) (hb : d85724 q = 1) : d88216 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5912, d88216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5912, d88216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5913 q = 1) (hb : d85724 q = 1) : d88217 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5913, d88217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5913, d88217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d5914 q = 1) (hb : d85724 q = 1) : d88218 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5914, d88218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5914, d88218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10295 (p : Pattern) (ha : d330 p = 1) (hb : d85723 p = 1) : d88223 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d328 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d144 q = 1) : d144 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d30 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d145 q = 1) (hb : d85721 q = 1) : d10649 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d85721, d10649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d145, d85721, d10649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d146 q = 1) (hb : d85721 q = 1) : d10650 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d10650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d146, d10650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147 q = 1) (hb : d85721 q = 1) : d10651 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d10651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d147, d10651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33 q = 1) (hb : d85721 q = 1) : d33 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d148 q = 1) (hb : d85721 q = 1) : d10652 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148, d10652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148, d10652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d329 q = 1) (hb : d85723 q = 1) : d88222 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d329, d85723, d88222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d329, d85723, d88222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d330 q = 1) (hb : d85723 q = 1) : d88223 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d330, d88223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d330, d88223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro10296 (p : Pattern) (ha : d5921 p = 1) (hb : d85724 p = 1) : d88229 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d331 q = 1) (hb : d85723 q = 1) : d88224 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d331, d88224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10295 q ha hb
    | true =>
      simp only [d331, d88224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d332 q = 1) (hb : d85723 q = 1) : d88225 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d332, d88225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d332, d88225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5918 q = 1) (hb : d85724 q = 1) : d88226 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5918, d85724, d88226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5918, d85724, d88226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5919 q = 1) (hb : d85724 q = 1) : d88227 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5919, d88227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5919, d88227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d5920 q = 1) (hb : d85724 q = 1) : d88228 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5920, d88228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5920, d88228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d5921 q = 1) (hb : d85724 q = 1) : d88229 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5921, d88229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5921, d88229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10297 (p : Pattern) (ha : d76825 p = 1) (hb : d85724 p = 1) : d88235 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5908 q = 1) (hb : d85724 q = 1) : d88212 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5908, d88212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10293 q ha hb
    | true =>
      simp only [d5908, d88212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10274 q ha hb
  have h2 (q : Pattern) (ha : d5909 q = 1) (hb : d85724 q = 1) : d88213 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5909, d88213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5909, d88213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5910 q = 1) (hb : d85724 q = 1) : d88214 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5910, d88214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5910, d88214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5911 q = 1) (hb : d85724 q = 1) : d88215 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5911, d88215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5911, d88215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5915 q = 1) (hb : d85724 q = 1) : d88219 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5915, d88219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10294 q ha hb
    | true =>
      simp only [d5915, d88219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10275 q ha hb
  have h6 (q : Pattern) (ha : d5916 q = 1) (hb : d85724 q = 1) : d88220 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5916, d88220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5916, d88220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5917 q = 1) (hb : d85724 q = 1) : d88221 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5917, d88221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5917, d88221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d5922 q = 1) (hb : d85724 q = 1) : d88230 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5922, d88230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10296 q ha hb
    | true =>
      simp only [d5922, d88230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10277 q ha hb
  have h9 (q : Pattern) (ha : d76821 q = 1) (hb : d85724 q = 1) : d88231 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76821, d88231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76821, d88231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d4737 q = 1) (hb : d85724 q = 1) : d88147 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10277 q ha hb
    | true =>
      simp only [d4737, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5350 q = 1) (hb : d85724 q = 1) : d88148 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, d88148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5350, d88148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d76822 q = 1) (hb : d85724 q = 1) : d88232 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76822, d88232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76822, d88232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d76823 q = 1) (hb : d85724 q = 1) : d88233 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76823, d88233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d76823, d88233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d76824 q = 1) (hb : d85724 q = 1) : d88234 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76824, d88234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76824, d88234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76825 q = 1) (hb : d85724 q = 1) : d88235 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76825, d88235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76825, d88235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro10298 (p : Pattern) (ha : d5933 p = 1) (hb : d85724 p = 1) : d88236 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d151 q = 1) (hb : d85723 q = 1) : d88141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10276 q ha hb
    | true =>
      simp only [d151, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d152 q = 1) (hb : d85723 q = 1) : d88142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d152, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4733 q = 1) (hb : d85724 q = 1) : d88143 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d85724, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4733, d85724, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4734 q = 1) (hb : d85724 q = 1) : d88144 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4734, d88144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4734, d88144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d5906 q = 1) (hb : d85724 q = 1) : d88210 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5906, d88210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5906, d88210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5933 q = 1) (hb : d85724 q = 1) : d88236 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5933, d88236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5933, d88236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro10299 (p : Pattern) (ha : d5938 p = 1) (hb : d85724 p = 1) : d88241 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d151 q = 1) (hb : d85723 q = 1) : d88141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10276 q ha hb
    | true =>
      simp only [d151, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d152 q = 1) (hb : d85723 q = 1) : d88142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d152, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4733 q = 1) (hb : d85724 q = 1) : d88143 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d85724, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4733, d85724, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5912 q = 1) (hb : d85724 q = 1) : d88216 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5912, d88216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5912, d88216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5913 q = 1) (hb : d85724 q = 1) : d88217 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5913, d88217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5913, d88217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d5938 q = 1) (hb : d85724 q = 1) : d88241 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5938, d88241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5938, d88241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro10300 (p : Pattern) (ha : d5942 p = 1) (hb : d85724 p = 1) : d88245 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d331 q = 1) (hb : d85723 q = 1) : d88224 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d331, d88224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10295 q ha hb
    | true =>
      simp only [d331, d88224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d332 q = 1) (hb : d85723 q = 1) : d88225 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d332, d88225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d332, d88225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5918 q = 1) (hb : d85724 q = 1) : d88226 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5918, d85724, d88226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5918, d85724, d88226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d5919 q = 1) (hb : d85724 q = 1) : d88227 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5919, d88227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5919, d88227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5920 q = 1) (hb : d85724 q = 1) : d88228 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5920, d88228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5920, d88228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d5942 q = 1) (hb : d85724 q = 1) : d88245 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5942, d88245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5942, d88245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro10301 (p : Pattern) (ha : d76830 p = 1) (hb : d85724 p = 1) : d88251 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5908 q = 1) (hb : d85724 q = 1) : d88212 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5908, d88212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10293 q ha hb
    | true =>
      simp only [d5908, d88212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10274 q ha hb
  have h2 (q : Pattern) (ha : d5909 q = 1) (hb : d85724 q = 1) : d88213 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5909, d88213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5909, d88213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5910 q = 1) (hb : d85724 q = 1) : d88214 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5910, d88214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5910, d88214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5911 q = 1) (hb : d85724 q = 1) : d88215 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5911, d88215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5911, d88215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5915 q = 1) (hb : d85724 q = 1) : d88219 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5915, d88219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10294 q ha hb
    | true =>
      simp only [d5915, d88219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10275 q ha hb
  have h6 (q : Pattern) (ha : d5916 q = 1) (hb : d85724 q = 1) : d88220 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5916, d88220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5916, d88220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5917 q = 1) (hb : d85724 q = 1) : d88221 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5917, d88221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5917, d88221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d5922 q = 1) (hb : d85724 q = 1) : d88230 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5922, d88230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10296 q ha hb
    | true =>
      simp only [d5922, d88230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10277 q ha hb
  have h9 (q : Pattern) (ha : d76821 q = 1) (hb : d85724 q = 1) : d88231 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76821, d88231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76821, d88231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d4737 q = 1) (hb : d85724 q = 1) : d88147 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10277 q ha hb
    | true =>
      simp only [d4737, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5350 q = 1) (hb : d85724 q = 1) : d88148 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, d88148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5350, d88148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d76822 q = 1) (hb : d85724 q = 1) : d88232 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76822, d88232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76822, d88232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d76823 q = 1) (hb : d85724 q = 1) : d88233 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76823, d88233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d76823, d88233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d76824 q = 1) (hb : d85724 q = 1) : d88234 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76824, d88234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76824, d88234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d5934 q = 1) (hb : d85724 q = 1) : d88237 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5934, d88237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10298 q ha hb
    | true =>
      simp only [d5934, d88237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10279 q ha hb
  have h16 (q : Pattern) (ha : d5935 q = 1) (hb : d85724 q = 1) : d88238 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5935, d88238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5935, d88238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d5936 q = 1) (hb : d85724 q = 1) : d88239 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5936, d88239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d5936, d88239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d5937 q = 1) (hb : d85724 q = 1) : d88240 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5937, d88240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5937, d88240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d5939 q = 1) (hb : d85724 q = 1) : d88242 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5939, d88242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10299 q ha hb
    | true =>
      simp only [d5939, d88242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10280 q ha hb
  have h20 (q : Pattern) (ha : d5940 q = 1) (hb : d85724 q = 1) : d88243 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5940, d88243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5940, d88243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d5941 q = 1) (hb : d85724 q = 1) : d88244 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5941, d88244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d5941, d88244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d5943 q = 1) (hb : d85724 q = 1) : d88246 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5943, d88246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10300 q ha hb
    | true =>
      simp only [d5943, d88246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10281 q ha hb
  have h23 (q : Pattern) (ha : d76826 q = 1) (hb : d85724 q = 1) : d88247 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76826, d88247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d76826, d88247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d5356 q = 1) (hb : d85724 q = 1) : d88154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10281 q ha hb
    | true =>
      simp only [d5356, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d5357 q = 1) (hb : d85724 q = 1) : d88155 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, d88155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d5357, d88155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d76827 q = 1) (hb : d85724 q = 1) : d88248 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76827, d88248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d76827, d88248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d76828 q = 1) (hb : d85724 q = 1) : d88249 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76828, d88249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d76828, d88249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d76829 q = 1) (hb : d85724 q = 1) : d88250 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76829, d88250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d76829, d88250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d76830 q = 1) (hb : d85724 q = 1) : d88251 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76830, d88251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d76830, d88251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro10302 (p : Pattern) (ha : d76837 p = 1) (hb : d85724 p = 1) : d88260 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5943 q = 1) (hb : d85724 q = 1) : d88246 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5943, d88246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10300 q ha hb
    | true =>
      simp only [d5943, d88246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10281 q ha hb
  have h2 (q : Pattern) (ha : d76826 q = 1) (hb : d85724 q = 1) : d88247 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76826, d88247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76826, d88247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5356 q = 1) (hb : d85724 q = 1) : d88154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10281 q ha hb
    | true =>
      simp only [d5356, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5357 q = 1) (hb : d85724 q = 1) : d88155 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, d88155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5357, d88155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d76827 q = 1) (hb : d85724 q = 1) : d88248 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76827, d88248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76827, d88248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76835 q = 1) (hb : d85724 q = 1) : d88258 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76835, d88258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76835, d88258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76836 q = 1) (hb : d85724 q = 1) : d88259 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76836, d88259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76836, d88259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76837 q = 1) (hb : d85724 q = 1) : d88260 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76837, d88260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76837, d88260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10303 (p : Pattern) (ha : d423 p = 1) (hb : d85723 p = 1) : d88267 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d421 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d231 q = 1) : d231 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d71 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d232 q = 1) (hb : d85721 q = 1) : d10686 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d85721, d10686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d232, d85721, d10686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d233 q = 1) (hb : d85721 q = 1) : d10687 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d10687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d233, d10687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234 q = 1) (hb : d85721 q = 1) : d10688 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d10688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d234, d10688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74 q = 1) (hb : d85721 q = 1) : d74 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d235 q = 1) (hb : d85721 q = 1) : d10689 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, d10689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d235, d10689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d422 q = 1) (hb : d85723 q = 1) : d88266 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d422, d85723, d88266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d422, d85723, d88266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d423 q = 1) (hb : d85723 q = 1) : d88267 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d423, d88267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d423, d88267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro10304 (p : Pattern) (ha : d5968 p = 1) (hb : d85724 p = 1) : d88273 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d424 q = 1) (hb : d85723 q = 1) : d88268 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d424, d88268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10303 q ha hb
    | true =>
      simp only [d424, d88268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d425 q = 1) (hb : d85723 q = 1) : d88269 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d425, d88269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d425, d88269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5965 q = 1) (hb : d85724 q = 1) : d88270 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5965, d85724, d88270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5965, d85724, d88270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d5966 q = 1) (hb : d85724 q = 1) : d88271 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5966, d88271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5966, d88271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5967 q = 1) (hb : d85724 q = 1) : d88272 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5967, d88272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5967, d88272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d5968 q = 1) (hb : d85724 q = 1) : d88273 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5968, d88273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5968, d88273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro10305 (p : Pattern) (ha : d76847 p = 1) (hb : d85724 p = 1) : d88279 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5969 q = 1) (hb : d85724 q = 1) : d88274 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5969, d88274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10304 q ha hb
    | true =>
      simp only [d5969, d88274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10285 q ha hb
  have h2 (q : Pattern) (ha : d76843 q = 1) (hb : d85724 q = 1) : d88275 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76843, d88275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76843, d88275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5378 q = 1) (hb : d85724 q = 1) : d88178 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5378, d88178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10285 q ha hb
    | true =>
      simp only [d5378, d88178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5379 q = 1) (hb : d85724 q = 1) : d88179 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5379, d88179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5379, d88179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d76844 q = 1) (hb : d85724 q = 1) : d88276 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76844, d88276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76844, d88276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76845 q = 1) (hb : d85724 q = 1) : d88277 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76845, d88277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76845, d88277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76846 q = 1) (hb : d85724 q = 1) : d88278 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76846, d88278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76846, d88278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76847 q = 1) (hb : d85724 q = 1) : d88279 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76847, d88279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76847, d88279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10306 (p : Pattern) (ha : d76853 p = 1) (hb : d85724 p = 1) : d88285 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5896 q = 1) (hb : d85724 q = 1) : d88200 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d5896, d88200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5896, d88200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10290 q ha hb
  have h2 (q : Pattern) (ha : d5897 q = 1) (hb : d85724 q = 1) : d88201 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d5897, d88201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5897, d88201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5903 q = 1) (hb : d85724 q = 1) : d88207 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d5903, d88207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10290 q ha hb
    | true =>
      simp only [d5903, d88207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10291 q ha hb
  have h4 (q : Pattern) (ha : d5904 q = 1) (hb : d85724 q = 1) : d88208 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d5904, d88208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5904, d88208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5905 q = 1) (hb : d85724 q = 1) : d88209 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d5905, d88209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5905, d88209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76831 q = 1) (hb : d85724 q = 1) : d88252 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76831, d88252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10297 q ha hb
    | true =>
      simp only [d76831, d88252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10301 q ha hb
  have h7 (q : Pattern) (ha : d5953 q = 1) (hb : d85724 q = 1) : d88254 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d5953, d88254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10292 q ha hb
    | true =>
      simp only [d5953, d88254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10272 q ha hb
  have h8 (q : Pattern) (ha : d76832 q = 1) (hb : d85724 q = 1) : d88255 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76832, d88255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76832, d88255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76833 q = 1) (hb : d85724 q = 1) : d88256 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76833, d88256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76833, d88256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d76834 q = 1) (hb : d85724 q = 1) : d88257 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76834, d88257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76834, d88257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d76838 q = 1) (hb : d85724 q = 1) : d88261 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76838, d88261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76838, d88261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10302 q ha hb
  have h12 (q : Pattern) (ha : d407 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10288 q ha hb
  have h13 (q : Pattern) (ha : d76839 q = 1) (hb : d85724 q = 1) : d88262 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76839, d88262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76839, d88262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d76840 q = 1) (hb : d85724 q = 1) : d88263 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76840, d88263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76840, d88263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d76841 q = 1) (hb : d85724 q = 1) : d88264 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76841, d88264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d76841, d88264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d76842 q = 1) (hb : d85724 q = 1) : d88265 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76842, d88265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76842, d88265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d76848 q = 1) (hb : d85724 q = 1) : d88280 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76848, d88280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76848, d88280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10305 q ha hb
  have h18 (q : Pattern) (ha : d463 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10289 q ha hb
  have h19 (q : Pattern) (ha : d76849 q = 1) (hb : d85724 q = 1) : d88281 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76849, d88281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d76849, d88281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d76850 q = 1) (hb : d85724 q = 1) : d88282 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76850, d88282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d76850, d88282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d76851 q = 1) (hb : d85724 q = 1) : d88283 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76851, d88283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d76851, d88283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d76852 q = 1) (hb : d85724 q = 1) : d88284 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76852, d88284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d76852, d88284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d76853 q = 1) (hb : d85724 q = 1) : d88285 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d76853, d88285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d76853, d88285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro10307 (p : Pattern) (ha : d76859 p = 1) (hb : d85724 p = 1) : d88291 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10270 q ha hb
  have h2 (q : Pattern) (ha : d97 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d98 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76816 q = 1) (hb : d85724 q = 1) : d88190 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d76816, d88190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76816, d88190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10287 q ha hb
  have h6 (q : Pattern) (ha : d76817 q = 1) (hb : d85724 q = 1) : d88191 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d76817, d88191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76817, d88191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76818 q = 1) (hb : d85724 q = 1) : d88192 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d76818, d88192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76818, d88192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76819 q = 1) (hb : d85724 q = 1) : d88193 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d76819, d88193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76819, d88193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76820 q = 1) (hb : d85724 q = 1) : d88194 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d76820, d88194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76820, d88194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d76854 q = 1) (hb : d85724 q = 1) : d88286 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d76854, d88286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76854, d88286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10306 q ha hb
  have h11 (q : Pattern) (ha : d76855 q = 1) (hb : d85724 q = 1) : d88287 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d76855, d88287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76855, d88287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d76856 q = 1) (hb : d85724 q = 1) : d88288 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d76856, d88288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76856, d88288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d76857 q = 1) (hb : d85724 q = 1) : d88289 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d76857, d88289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76857, d88289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d76858 q = 1) (hb : d85724 q = 1) : d88290 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d76858, d88290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76858, d88290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76859 q = 1) (hb : d85724 q = 1) : d88291 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d76859, d88291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76859, d88291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro10308 (p : Pattern) (ha : d481 p = 1) (hb : d85723 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d475 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d480 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d480, d85723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d480, d85723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d481 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro10309 (p : Pattern) (ha : d491 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d482 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10308 q ha hb
    | true =>
      simp only [d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d483 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d488 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d488, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d489 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d490 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d491 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10310 (p : Pattern) (ha : d501 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10308 q ha hb
    | true =>
      simp only [d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d488 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d489 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d490 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d501 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro10311 (p : Pattern) (ha : d644 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d633 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10309 q ha hb
    | true =>
      simp only [d633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d634 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d635 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d636 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d637 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d639 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10310 q ha hb
    | true =>
      simp only [d639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d640 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d641 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d642 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d643 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d644 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
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
theorem andIntro10312 (p : Pattern) (ha : d653 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d639 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10310 q ha hb
    | true =>
      simp only [d639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d640 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d641 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d642 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d643 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d653 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
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
theorem andIntro10313 (p : Pattern) (ha : d683 p = 1) (hb : d85723 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d673 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d682 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d682, d85723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d682, d85723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d683 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro10314 (p : Pattern) (ha : d730 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d684 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10313 q ha hb
    | true =>
      simp only [d684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d685 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d727 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d727, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d727, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d728 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d729 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d730 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro10315 (p : Pattern) (ha : d736 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d731 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10314 q ha hb
    | true =>
      simp only [d731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d732 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d733 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d734 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d735 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d736 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
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
theorem andIntro10316 (p : Pattern) (ha : d477 p = 1) (hb : d85723 p = 1) : d88293 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d328 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d144 q = 1) : d144 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d30 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d145 q = 1) (hb : d85721 q = 1) : d10649 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d85721, d10649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d145, d85721, d10649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d146 q = 1) (hb : d85721 q = 1) : d10650 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d10650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d146, d10650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147 q = 1) (hb : d85721 q = 1) : d10651 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d10651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d147, d10651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d475 q = 1) (hb : d85721 q = 1) : d10863 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, d10863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d475, d10863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d476 q = 1) (hb : d85723 q = 1) : d88292 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d476, d85723, d88292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d476, d85723, d88292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d477 q = 1) (hb : d85723 q = 1) : d88293 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d477, d88293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d477, d88293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro10317 (p : Pattern) (ha : d5399 p = 1) (hb : d85724 p = 1) : d88299 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d478 q = 1) (hb : d85723 q = 1) : d88294 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10316 q ha hb
    | true =>
      simp only [d478, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d479 q = 1) (hb : d85723 q = 1) : d88295 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d479, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5396 q = 1) (hb : d85724 q = 1) : d88296 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5396, d85724, d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5396, d85724, d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5397 q = 1) (hb : d85724 q = 1) : d88297 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5397, d88297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5397, d88297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d5398 q = 1) (hb : d85724 q = 1) : d88298 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5398, d88298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5398, d88298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d5399 q = 1) (hb : d85724 q = 1) : d88299 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5399, d88299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5399, d88299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10318 (p : Pattern) (ha : d5997 p = 1) (hb : d85724 p = 1) : d88305 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5992 q = 1) (hb : d85724 q = 1) : d88300 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5992, d88300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10317 q ha hb
    | true =>
      simp only [d5992, d88300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10309 q ha hb
  have h2 (q : Pattern) (ha : d5993 q = 1) (hb : d85724 q = 1) : d88301 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5993, d88301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5993, d88301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5994 q = 1) (hb : d85724 q = 1) : d88302 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5994, d88302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5994, d88302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5995 q = 1) (hb : d85724 q = 1) : d88303 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5995, d88303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5995, d88303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5996 q = 1) (hb : d85724 q = 1) : d88304 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5996, d88304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5996, d88304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5997 q = 1) (hb : d85724 q = 1) : d88305 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d5997, d88305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5997, d88305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10319 (p : Pattern) (ha : d5406 p = 1) (hb : d85724 p = 1) : d88308 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d478 q = 1) (hb : d85723 q = 1) : d88294 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10316 q ha hb
    | true =>
      simp only [d478, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d479 q = 1) (hb : d85723 q = 1) : d88295 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d479, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5396 q = 1) (hb : d85724 q = 1) : d88296 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5396, d85724, d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5396, d85724, d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d5397 q = 1) (hb : d85724 q = 1) : d88297 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5397, d88297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5397, d88297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5398 q = 1) (hb : d85724 q = 1) : d88298 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5398, d88298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5398, d88298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d5406 q = 1) (hb : d85724 q = 1) : d88308 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5406, d88308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5406, d88308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro10320 (p : Pattern) (ha : d6005 p = 1) (hb : d85724 p = 1) : d88314 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5992 q = 1) (hb : d85724 q = 1) : d88300 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5992, d88300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10317 q ha hb
    | true =>
      simp only [d5992, d88300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10309 q ha hb
  have h2 (q : Pattern) (ha : d5993 q = 1) (hb : d85724 q = 1) : d88301 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5993, d88301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5993, d88301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5994 q = 1) (hb : d85724 q = 1) : d88302 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5994, d88302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5994, d88302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5995 q = 1) (hb : d85724 q = 1) : d88303 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5995, d88303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5995, d88303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5996 q = 1) (hb : d85724 q = 1) : d88304 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5996, d88304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5996, d88304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6000 q = 1) (hb : d85724 q = 1) : d88309 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6000, d88309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10319 q ha hb
    | true =>
      simp only [d6000, d88309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10310 q ha hb
  have h7 (q : Pattern) (ha : d6001 q = 1) (hb : d85724 q = 1) : d88310 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6001, d88310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6001, d88310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6002 q = 1) (hb : d85724 q = 1) : d88311 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6002, d88311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6002, d88311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d6003 q = 1) (hb : d85724 q = 1) : d88312 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6003, d88312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6003, d88312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6004 q = 1) (hb : d85724 q = 1) : d88313 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6004, d88313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6004, d88313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6005 q = 1) (hb : d85724 q = 1) : d88314 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6005, d88314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6005, d88314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro10321 (p : Pattern) (ha : d4824 p = 1) (hb : d85723 p = 1) : d88343 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d328 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d4818 q = 1) : d4818 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d30 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4819 q = 1) (hb : d85721 q = 1) : d88338 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4819, d85721, d88338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d4819, d85721, d88338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d4820 q = 1) (hb : d85721 q = 1) : d88339 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4820, d88339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4820, d88339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4821 q = 1) (hb : d85721 q = 1) : d88340 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4821, d88340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4821, d88340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4822 q = 1) (hb : d85721 q = 1) : d88341 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d4822, d88341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4822, d88341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d4823 q = 1) (hb : d85723 q = 1) : d88342 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d4823, d85723, d88342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d4823, d85723, d88342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d4824 q = 1) (hb : d85723 q = 1) : d88343 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d4824, d88343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4824, d88343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro10322 (p : Pattern) (ha : d4830 p = 1) (hb : d85724 p = 1) : d88349 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4825 q = 1) (hb : d85723 q = 1) : d88344 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d4825, d88344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10321 q ha hb
    | true =>
      simp only [d4825, d88344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4826 q = 1) (hb : d85723 q = 1) : d88345 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d4826, d88345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4826, d88345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4827 q = 1) (hb : d85724 q = 1) : d88346 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4827, d85724, d88346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4827, d85724, d88346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4828 q = 1) (hb : d85724 q = 1) : d88347 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4828, d88347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4828, d88347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d4829 q = 1) (hb : d85724 q = 1) : d88348 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4829, d88348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4829, d88348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d4830 q = 1) (hb : d85724 q = 1) : d88349 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d4830, d88349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4830, d88349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10323 (p : Pattern) (ha : d6061 p = 1) (hb : d85724 p = 1) : d88381 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6056 q = 1) (hb : d85724 q = 1) : d88376 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6056, d88376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10322 q ha hb
    | true =>
      simp only [d6056, d88376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10309 q ha hb
  have h2 (q : Pattern) (ha : d6057 q = 1) (hb : d85724 q = 1) : d88377 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6057, d88377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6057, d88377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6058 q = 1) (hb : d85724 q = 1) : d88378 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6058, d88378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6058, d88378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6059 q = 1) (hb : d85724 q = 1) : d88379 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6059, d88379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6059, d88379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6060 q = 1) (hb : d85724 q = 1) : d88380 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6060, d88380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6060, d88380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d633 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10309 q ha hb
    | true =>
      simp only [d633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d634 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d635 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d636 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d637 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6061 q = 1) (hb : d85724 q = 1) : d88381 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6061, d88381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6061, d88381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro10324 (p : Pattern) (ha : d514 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d482 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10308 q ha hb
    | true =>
      simp only [d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d483 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d488 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d488, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d489 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d513 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d514 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10325 (p : Pattern) (ha : d524 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d482 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10308 q ha hb
    | true =>
      simp only [d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d483 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d488 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d488, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d522 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d523 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d524 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10326 (p : Pattern) (ha : d6010 p = 1) (hb : d85724 p = 1) : d88319 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d478 q = 1) (hb : d85723 q = 1) : d88294 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10316 q ha hb
    | true =>
      simp only [d478, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d479 q = 1) (hb : d85723 q = 1) : d88295 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d479, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5396 q = 1) (hb : d85724 q = 1) : d88296 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5396, d85724, d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5396, d85724, d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5397 q = 1) (hb : d85724 q = 1) : d88297 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5397, d88297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5397, d88297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6009 q = 1) (hb : d85724 q = 1) : d88318 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6009, d88318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6009, d88318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6010 q = 1) (hb : d85724 q = 1) : d88319 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6010, d88319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6010, d88319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10327 (p : Pattern) (ha : d6017 p = 1) (hb : d85724 p = 1) : d88326 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d478 q = 1) (hb : d85723 q = 1) : d88294 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10316 q ha hb
    | true =>
      simp only [d478, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d479 q = 1) (hb : d85723 q = 1) : d88295 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d479, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5396 q = 1) (hb : d85724 q = 1) : d88296 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5396, d85724, d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5396, d85724, d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6015 q = 1) (hb : d85724 q = 1) : d88324 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6015, d88324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6015, d88324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6016 q = 1) (hb : d85724 q = 1) : d88325 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6016, d88325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6016, d88325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6017 q = 1) (hb : d85724 q = 1) : d88326 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6017, d88326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6017, d88326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10328 (p : Pattern) (ha : d554 p = 1) (hb : d85723 p = 1) : d88331 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d552 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d324 q = 1) : d324 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d144 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d325 q = 1) (hb : d85721 q = 1) : d10742 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d325, d85721, d10742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d325, d85721, d10742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d326 q = 1) (hb : d85721 q = 1) : d10743 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d326, d10743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d326, d10743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d327 q = 1) (hb : d85721 q = 1) : d10744 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d327, d10744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d327, d10744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d144 q = 1) : d144 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d30 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d145 q = 1) (hb : d85721 q = 1) : d10649 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d85721, d10649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d145, d85721, d10649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d146 q = 1) (hb : d85721 q = 1) : d10650 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d10650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d146, d10650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147 q = 1) (hb : d85721 q = 1) : d10651 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d10651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d147, d10651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d328 q = 1) (hb : d85721 q = 1) : d10745 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d328, d10745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d328, d10745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d553 q = 1) (hb : d85723 q = 1) : d88330 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d553, d85723, d88330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d553, d85723, d88330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d554 q = 1) (hb : d85723 q = 1) : d88331 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d554, d88331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d554, d88331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro10329 (p : Pattern) (ha : d6024 p = 1) (hb : d85724 p = 1) : d88337 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d555 q = 1) (hb : d85723 q = 1) : d88332 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d555, d88332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10328 q ha hb
    | true =>
      simp only [d555, d88332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d556 q = 1) (hb : d85723 q = 1) : d88333 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d556, d88333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d556, d88333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6021 q = 1) (hb : d85724 q = 1) : d88334 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6021, d85724, d88334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6021, d85724, d88334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6022 q = 1) (hb : d85724 q = 1) : d88335 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6022, d88335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6022, d88335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6023 q = 1) (hb : d85724 q = 1) : d88336 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6023, d88336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6023, d88336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6024 q = 1) (hb : d85724 q = 1) : d88337 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6024, d88337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6024, d88337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10330 (p : Pattern) (ha : d76864 p = 1) (hb : d85724 p = 1) : d88356 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6011 q = 1) (hb : d85724 q = 1) : d88320 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6011, d88320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10326 q ha hb
    | true =>
      simp only [d6011, d88320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10324 q ha hb
  have h2 (q : Pattern) (ha : d6012 q = 1) (hb : d85724 q = 1) : d88321 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6012, d88321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6012, d88321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6013 q = 1) (hb : d85724 q = 1) : d88322 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6013, d88322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6013, d88322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6014 q = 1) (hb : d85724 q = 1) : d88323 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6014, d88323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6014, d88323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6018 q = 1) (hb : d85724 q = 1) : d88327 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6018, d88327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10327 q ha hb
    | true =>
      simp only [d6018, d88327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10325 q ha hb
  have h6 (q : Pattern) (ha : d6019 q = 1) (hb : d85724 q = 1) : d88328 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6019, d88328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6019, d88328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6020 q = 1) (hb : d85724 q = 1) : d88329 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6020, d88329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6020, d88329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6025 q = 1) (hb : d85724 q = 1) : d88350 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6025, d88350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10329 q ha hb
    | true =>
      simp only [d6025, d88350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10322 q ha hb
  have h9 (q : Pattern) (ha : d76860 q = 1) (hb : d85724 q = 1) : d88351 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76860, d88351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76860, d88351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d5400 q = 1) (hb : d85724 q = 1) : d88300 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5400, d88300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10317 q ha hb
    | true =>
      simp only [d5400, d88300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5401 q = 1) (hb : d85724 q = 1) : d88352 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5401, d88352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5401, d88352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d76861 q = 1) (hb : d85724 q = 1) : d88353 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76861, d88353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76861, d88353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d76862 q = 1) (hb : d85724 q = 1) : d88354 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76862, d88354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d76862, d88354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d76863 q = 1) (hb : d85724 q = 1) : d88355 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76863, d88355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76863, d88355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76864 q = 1) (hb : d85724 q = 1) : d88356 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76864, d88356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76864, d88356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro10331 (p : Pattern) (ha : d610 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d482 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10308 q ha hb
    | true =>
      simp only [d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d483 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d488 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d488, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d489 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d513 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d610 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro10332 (p : Pattern) (ha : d616 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d482 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10308 q ha hb
    | true =>
      simp only [d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d483 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d488 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d488, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d522 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d523 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d616 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro10333 (p : Pattern) (ha : d6036 p = 1) (hb : d85724 p = 1) : d88357 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d478 q = 1) (hb : d85723 q = 1) : d88294 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10316 q ha hb
    | true =>
      simp only [d478, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d479 q = 1) (hb : d85723 q = 1) : d88295 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d479, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5396 q = 1) (hb : d85724 q = 1) : d88296 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5396, d85724, d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5396, d85724, d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5397 q = 1) (hb : d85724 q = 1) : d88297 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5397, d88297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5397, d88297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6009 q = 1) (hb : d85724 q = 1) : d88318 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6009, d88318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6009, d88318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6036 q = 1) (hb : d85724 q = 1) : d88357 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6036, d88357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6036, d88357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro10334 (p : Pattern) (ha : d6041 p = 1) (hb : d85724 p = 1) : d88362 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d478 q = 1) (hb : d85723 q = 1) : d88294 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10316 q ha hb
    | true =>
      simp only [d478, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d479 q = 1) (hb : d85723 q = 1) : d88295 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d479, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5396 q = 1) (hb : d85724 q = 1) : d88296 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5396, d85724, d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5396, d85724, d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6015 q = 1) (hb : d85724 q = 1) : d88324 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6015, d88324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6015, d88324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6016 q = 1) (hb : d85724 q = 1) : d88325 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6016, d88325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6016, d88325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6041 q = 1) (hb : d85724 q = 1) : d88362 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6041, d88362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6041, d88362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro10335 (p : Pattern) (ha : d6045 p = 1) (hb : d85724 p = 1) : d88366 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d555 q = 1) (hb : d85723 q = 1) : d88332 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d555, d88332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10328 q ha hb
    | true =>
      simp only [d555, d88332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d556 q = 1) (hb : d85723 q = 1) : d88333 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d556, d88333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d556, d88333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6021 q = 1) (hb : d85724 q = 1) : d88334 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6021, d85724, d88334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6021, d85724, d88334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6022 q = 1) (hb : d85724 q = 1) : d88335 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6022, d88335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6022, d88335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6023 q = 1) (hb : d85724 q = 1) : d88336 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6023, d88336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6023, d88336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6045 q = 1) (hb : d85724 q = 1) : d88366 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6045, d88366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6045, d88366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro10336 (p : Pattern) (ha : d6046 p = 1) (hb : d85724 p = 1) : d88367 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4825 q = 1) (hb : d85723 q = 1) : d88344 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d4825, d88344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10321 q ha hb
    | true =>
      simp only [d4825, d88344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4826 q = 1) (hb : d85723 q = 1) : d88345 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d4826, d88345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4826, d88345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4827 q = 1) (hb : d85724 q = 1) : d88346 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4827, d85724, d88346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4827, d85724, d88346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d4828 q = 1) (hb : d85724 q = 1) : d88347 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4828, d88347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4828, d88347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4829 q = 1) (hb : d85724 q = 1) : d88348 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4829, d88348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4829, d88348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6046 q = 1) (hb : d85724 q = 1) : d88367 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6046, d88367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6046, d88367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro10337 (p : Pattern) (ha : d76869 p = 1) (hb : d85724 p = 1) : d88374 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6011 q = 1) (hb : d85724 q = 1) : d88320 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6011, d88320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10326 q ha hb
    | true =>
      simp only [d6011, d88320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10324 q ha hb
  have h2 (q : Pattern) (ha : d6012 q = 1) (hb : d85724 q = 1) : d88321 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6012, d88321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6012, d88321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6013 q = 1) (hb : d85724 q = 1) : d88322 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6013, d88322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6013, d88322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6014 q = 1) (hb : d85724 q = 1) : d88323 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6014, d88323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6014, d88323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6018 q = 1) (hb : d85724 q = 1) : d88327 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6018, d88327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10327 q ha hb
    | true =>
      simp only [d6018, d88327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10325 q ha hb
  have h6 (q : Pattern) (ha : d6019 q = 1) (hb : d85724 q = 1) : d88328 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6019, d88328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6019, d88328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6020 q = 1) (hb : d85724 q = 1) : d88329 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6020, d88329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6020, d88329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6025 q = 1) (hb : d85724 q = 1) : d88350 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6025, d88350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10329 q ha hb
    | true =>
      simp only [d6025, d88350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10322 q ha hb
  have h9 (q : Pattern) (ha : d76860 q = 1) (hb : d85724 q = 1) : d88351 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76860, d88351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76860, d88351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d5400 q = 1) (hb : d85724 q = 1) : d88300 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5400, d88300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10317 q ha hb
    | true =>
      simp only [d5400, d88300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5401 q = 1) (hb : d85724 q = 1) : d88352 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5401, d88352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5401, d88352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d76861 q = 1) (hb : d85724 q = 1) : d88353 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76861, d88353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76861, d88353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d76862 q = 1) (hb : d85724 q = 1) : d88354 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76862, d88354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d76862, d88354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d76863 q = 1) (hb : d85724 q = 1) : d88355 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76863, d88355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76863, d88355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d6037 q = 1) (hb : d85724 q = 1) : d88358 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6037, d88358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10333 q ha hb
    | true =>
      simp only [d6037, d88358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10331 q ha hb
  have h16 (q : Pattern) (ha : d6038 q = 1) (hb : d85724 q = 1) : d88359 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6038, d88359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6038, d88359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d6039 q = 1) (hb : d85724 q = 1) : d88360 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6039, d88360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d6039, d88360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d6040 q = 1) (hb : d85724 q = 1) : d88361 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6040, d88361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6040, d88361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d6042 q = 1) (hb : d85724 q = 1) : d88363 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6042, d88363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10334 q ha hb
    | true =>
      simp only [d6042, d88363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10332 q ha hb
  have h20 (q : Pattern) (ha : d6043 q = 1) (hb : d85724 q = 1) : d88364 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6043, d88364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6043, d88364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d6044 q = 1) (hb : d85724 q = 1) : d88365 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6044, d88365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d6044, d88365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d6047 q = 1) (hb : d85724 q = 1) : d88368 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6047, d88368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10335 q ha hb
    | true =>
      simp only [d6047, d88368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10336 q ha hb
  have h23 (q : Pattern) (ha : d76865 q = 1) (hb : d85724 q = 1) : d88369 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76865, d88369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d76865, d88369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d5407 q = 1) (hb : d85724 q = 1) : d88309 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5407, d88309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10319 q ha hb
    | true =>
      simp only [d5407, d88309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d5408 q = 1) (hb : d85724 q = 1) : d88370 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5408, d88370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d5408, d88370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d76866 q = 1) (hb : d85724 q = 1) : d88371 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76866, d88371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d76866, d88371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d76867 q = 1) (hb : d85724 q = 1) : d88372 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76867, d88372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d76867, d88372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d76868 q = 1) (hb : d85724 q = 1) : d88373 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76868, d88373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d76868, d88373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d76869 q = 1) (hb : d85724 q = 1) : d88374 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76869, d88374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d76869, d88374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro10338 (p : Pattern) (ha : d76876 p = 1) (hb : d85724 p = 1) : d88388 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6047 q = 1) (hb : d85724 q = 1) : d88368 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6047, d88368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10335 q ha hb
    | true =>
      simp only [d6047, d88368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10336 q ha hb
  have h2 (q : Pattern) (ha : d76865 q = 1) (hb : d85724 q = 1) : d88369 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76865, d88369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76865, d88369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5407 q = 1) (hb : d85724 q = 1) : d88309 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5407, d88309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10319 q ha hb
    | true =>
      simp only [d5407, d88309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5408 q = 1) (hb : d85724 q = 1) : d88370 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5408, d88370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5408, d88370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d76866 q = 1) (hb : d85724 q = 1) : d88371 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76866, d88371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76866, d88371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76874 q = 1) (hb : d85724 q = 1) : d88386 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76874, d88386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76874, d88386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76875 q = 1) (hb : d85724 q = 1) : d88387 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76875, d88387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76875, d88387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76876 q = 1) (hb : d85724 q = 1) : d88388 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76876, d88388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76876, d88388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10339 (p : Pattern) (ha : d675 p = 1) (hb : d85723 p = 1) : d88417 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d421 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d231 q = 1) : d231 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d71 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d232 q = 1) (hb : d85721 q = 1) : d10686 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d85721, d10686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d232, d85721, d10686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d233 q = 1) (hb : d85721 q = 1) : d10687 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d10687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d233, d10687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234 q = 1) (hb : d85721 q = 1) : d10688 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d10688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d234, d10688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d673 q = 1) (hb : d85721 q = 1) : d11021 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d11021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d673, d11021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d674 q = 1) (hb : d85723 q = 1) : d88416 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d674, d85723, d88416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d674, d85723, d88416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d675 q = 1) (hb : d85723 q = 1) : d88417 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d675, d88417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d675, d88417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro10340 (p : Pattern) (ha : d5428 p = 1) (hb : d85724 p = 1) : d88423 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d676 q = 1) (hb : d85723 q = 1) : d88418 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d676, d88418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10339 q ha hb
    | true =>
      simp only [d676, d88418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d677 q = 1) (hb : d85723 q = 1) : d88419 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d677, d88419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d677, d88419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5425 q = 1) (hb : d85724 q = 1) : d88420 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5425, d85724, d88420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5425, d85724, d88420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d5426 q = 1) (hb : d85724 q = 1) : d88421 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5426, d88421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5426, d88421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5427 q = 1) (hb : d85724 q = 1) : d88422 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5427, d88422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5427, d88422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d5428 q = 1) (hb : d85724 q = 1) : d88423 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5428, d88423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5428, d88423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro10341 (p : Pattern) (ha : d670 p = 1) (hb : d85723 p = 1) : d88395 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d668 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d417 q = 1) : d417 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d231 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d418 q = 1) (hb : d85721 q = 1) : d10814 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d418, d85721, d10814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d418, d85721, d10814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d419 q = 1) (hb : d85721 q = 1) : d10815 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d419, d10815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d419, d10815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d420 q = 1) (hb : d85721 q = 1) : d10816 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d420, d10816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d420, d10816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d231 q = 1) : d231 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d71 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d232 q = 1) (hb : d85721 q = 1) : d10686 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d85721, d10686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d232, d85721, d10686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d233 q = 1) (hb : d85721 q = 1) : d10687 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d10687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d233, d10687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d234 q = 1) (hb : d85721 q = 1) : d10688 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d10688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d234, d10688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d421 q = 1) (hb : d85721 q = 1) : d10817 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d421, d10817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d421, d10817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d669 q = 1) (hb : d85723 q = 1) : d88394 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d669, d85723, d88394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d669, d85723, d88394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d670 q = 1) (hb : d85723 q = 1) : d88395 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d670, d88395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d670, d88395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro10342 (p : Pattern) (ha : d6077 p = 1) (hb : d85724 p = 1) : d88401 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d671 q = 1) (hb : d85723 q = 1) : d88396 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d671, d88396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10341 q ha hb
    | true =>
      simp only [d671, d88396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d672 q = 1) (hb : d85723 q = 1) : d88397 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d672, d88397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d672, d88397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6074 q = 1) (hb : d85724 q = 1) : d88398 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6074, d85724, d88398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6074, d85724, d88398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6075 q = 1) (hb : d85724 q = 1) : d88399 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6075, d88399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6075, d88399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6076 q = 1) (hb : d85724 q = 1) : d88400 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6076, d88400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6076, d88400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6077 q = 1) (hb : d85724 q = 1) : d88401 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6077, d88401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6077, d88401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro10343 (p : Pattern) (ha : d6084 p = 1) (hb : d85723 p = 1) : d88407 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d421 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d6078 q = 1) : d6078 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d71 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6079 q = 1) (hb : d85721 q = 1) : d88402 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6079, d85721, d88402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d6079, d85721, d88402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d6080 q = 1) (hb : d85721 q = 1) : d88403 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6080, d88403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6080, d88403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6081 q = 1) (hb : d85721 q = 1) : d88404 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6081, d88404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6081, d88404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6082 q = 1) (hb : d85721 q = 1) : d88405 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6082, d88405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6082, d88405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d6083 q = 1) (hb : d85723 q = 1) : d88406 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6083, d85723, d88406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6083, d85723, d88406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d6084 q = 1) (hb : d85723 q = 1) : d88407 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6084, d88407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6084, d88407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro10344 (p : Pattern) (ha : d6090 p = 1) (hb : d85724 p = 1) : d88413 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6085 q = 1) (hb : d85723 q = 1) : d88408 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6085, d88408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10343 q ha hb
    | true =>
      simp only [d6085, d88408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6086 q = 1) (hb : d85723 q = 1) : d88409 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6086, d88409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6086, d88409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6087 q = 1) (hb : d85724 q = 1) : d88410 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6087, d85724, d88410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6087, d85724, d88410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6088 q = 1) (hb : d85724 q = 1) : d88411 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6088, d88411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6088, d88411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6089 q = 1) (hb : d85724 q = 1) : d88412 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6089, d88412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6089, d88412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6090 q = 1) (hb : d85724 q = 1) : d88413 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6090, d88413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6090, d88413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro10345 (p : Pattern) (ha : d76886 p = 1) (hb : d85724 p = 1) : d88429 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6091 q = 1) (hb : d85724 q = 1) : d88414 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6091, d88414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10342 q ha hb
    | true =>
      simp only [d6091, d88414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10344 q ha hb
  have h2 (q : Pattern) (ha : d76882 q = 1) (hb : d85724 q = 1) : d88415 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76882, d88415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76882, d88415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5429 q = 1) (hb : d85724 q = 1) : d88424 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5429, d88424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10340 q ha hb
    | true =>
      simp only [d5429, d88424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5430 q = 1) (hb : d85724 q = 1) : d88425 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5430, d88425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5430, d88425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d76883 q = 1) (hb : d85724 q = 1) : d88426 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76883, d88426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76883, d88426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76884 q = 1) (hb : d85724 q = 1) : d88427 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76884, d88427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76884, d88427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76885 q = 1) (hb : d85724 q = 1) : d88428 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76885, d88428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76885, d88428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76886 q = 1) (hb : d85724 q = 1) : d88429 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76886, d88429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76886, d88429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10346 (p : Pattern) (ha : d76892 p = 1) (hb : d85724 p = 1) : d88435 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5998 q = 1) (hb : d85724 q = 1) : d88306 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d5998, d88306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5998, d88306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10318 q ha hb
  have h2 (q : Pattern) (ha : d5999 q = 1) (hb : d85724 q = 1) : d88307 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d5999, d88307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5999, d88307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6006 q = 1) (hb : d85724 q = 1) : d88315 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6006, d88315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10318 q ha hb
    | true =>
      simp only [d6006, d88315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10320 q ha hb
  have h4 (q : Pattern) (ha : d6007 q = 1) (hb : d85724 q = 1) : d88316 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6007, d88316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6007, d88316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6008 q = 1) (hb : d85724 q = 1) : d88317 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d6008, d88317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6008, d88317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76870 q = 1) (hb : d85724 q = 1) : d88375 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76870, d88375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10330 q ha hb
    | true =>
      simp only [d76870, d88375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10337 q ha hb
  have h7 (q : Pattern) (ha : d6062 q = 1) (hb : d85724 q = 1) : d88382 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6062, d88382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10323 q ha hb
    | true =>
      simp only [d6062, d88382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10311 q ha hb
  have h8 (q : Pattern) (ha : d76871 q = 1) (hb : d85724 q = 1) : d88383 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76871, d88383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76871, d88383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76872 q = 1) (hb : d85724 q = 1) : d88384 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76872, d88384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76872, d88384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d76873 q = 1) (hb : d85724 q = 1) : d88385 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76873, d88385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76873, d88385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d76877 q = 1) (hb : d85724 q = 1) : d88389 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76877, d88389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76877, d88389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10338 q ha hb
  have h12 (q : Pattern) (ha : d654 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10312 q ha hb
  have h13 (q : Pattern) (ha : d76878 q = 1) (hb : d85724 q = 1) : d88390 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76878, d88390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76878, d88390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d76879 q = 1) (hb : d85724 q = 1) : d88391 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76879, d88391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76879, d88391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d76880 q = 1) (hb : d85724 q = 1) : d88392 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76880, d88392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d76880, d88392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d76881 q = 1) (hb : d85724 q = 1) : d88393 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76881, d88393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76881, d88393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d76887 q = 1) (hb : d85724 q = 1) : d88430 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76887, d88430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76887, d88430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10345 q ha hb
  have h18 (q : Pattern) (ha : d737 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10315 q ha hb
  have h19 (q : Pattern) (ha : d76888 q = 1) (hb : d85724 q = 1) : d88431 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76888, d88431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d76888, d88431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d76889 q = 1) (hb : d85724 q = 1) : d88432 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76889, d88432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d76889, d88432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d76890 q = 1) (hb : d85724 q = 1) : d88433 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76890, d88433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d76890, d88433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d76891 q = 1) (hb : d85724 q = 1) : d88434 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76891, d88434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d76891, d88434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d76892 q = 1) (hb : d85724 q = 1) : d88435 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d76892, d88435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d76892, d88435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro10347 (p : Pattern) (ha : d76898 p = 1) (hb : d85724 p = 1) : d88441 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76893 q = 1) (hb : d85724 q = 1) : d88436 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d76893, d88436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76893, d88436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10346 q ha hb
  have h2 (q : Pattern) (ha : d76894 q = 1) (hb : d85724 q = 1) : d88437 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d76894, d88437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76894, d88437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76895 q = 1) (hb : d85724 q = 1) : d88438 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d76895, d88438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76895, d88438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76896 q = 1) (hb : d85724 q = 1) : d88439 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d76896, d88439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76896, d88439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76897 q = 1) (hb : d85724 q = 1) : d88440 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d76897, d88440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76897, d88440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76898 q = 1) (hb : d85724 q = 1) : d88441 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d76898, d88441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76898, d88441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10348 (p : Pattern) (ha : d773 p = 1) (hb : d85723 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d767 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d772 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d772, d85723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d772, d85723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d773 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro10349 (p : Pattern) (ha : d783 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d774 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10348 q ha hb
    | true =>
      simp only [d774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d775 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d780 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d780, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d781 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d782 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d783 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10350 (p : Pattern) (ha : d793 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10348 q ha hb
    | true =>
      simp only [d774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d780 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d781 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d782 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d793 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro10351 (p : Pattern) (ha : d950 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d939 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10349 q ha hb
    | true =>
      simp only [d939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d940 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d941 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d942 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d943 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d945 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10350 q ha hb
    | true =>
      simp only [d945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d946 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d947 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d948 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d949 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d950 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro10352 (p : Pattern) (ha : d959 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d945 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10350 q ha hb
    | true =>
      simp only [d945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d946 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d947 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d948 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d949 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d959 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10353 (p : Pattern) (ha : d1005 p = 1) (hb : d85723 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d995 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1004 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1004, d85723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1004, d85723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1005 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro10354 (p : Pattern) (ha : d1063 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1006 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10353 q ha hb
    | true =>
      simp only [d1006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1007 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1060 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1060, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1060, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1061 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1062 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d1063 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro10355 (p : Pattern) (ha : d1069 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1064 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10354 q ha hb
    | true =>
      simp only [d1064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1065 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1066 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1067 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1068 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1069 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10356 (p : Pattern) (ha : d769 p = 1) (hb : d85723 p = 1) : d88444 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d766 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d758 q = 1) : d758 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d762 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d763 q = 1) (hb : d85721 q = 1) : d11099 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d85721, d11099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d763, d85721, d11099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d764 q = 1) (hb : d85721 q = 1) : d11100 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d11100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d764, d11100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d765 q = 1) (hb : d85721 q = 1) : d11101 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d11101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d765, d11101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d767 q = 1) (hb : d85721 q = 1) : d11103 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d767, d11103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d767, d11103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d768 q = 1) (hb : d85723 q = 1) : d88443 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d768, d85723, d88443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d768, d85723, d88443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d769 q = 1) (hb : d85723 q = 1) : d88444 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d769, d88444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d769, d88444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro10357 (p : Pattern) (ha : d6118 p = 1) (hb : d85724 p = 1) : d88450 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d770 q = 1) (hb : d85723 q = 1) : d88445 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d88445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10356 q ha hb
    | true =>
      simp only [d770, d88445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d771 q = 1) (hb : d85723 q = 1) : d88446 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d88446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d771, d88446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6115 q = 1) (hb : d85724 q = 1) : d88447 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6115, d85724, d88447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6115, d85724, d88447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6116 q = 1) (hb : d85724 q = 1) : d88448 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6116, d88448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6116, d88448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6117 q = 1) (hb : d85724 q = 1) : d88449 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6117, d88449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6117, d88449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6118 q = 1) (hb : d85724 q = 1) : d88450 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6118, d88450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6118, d88450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10358 (p : Pattern) (ha : d6124 p = 1) (hb : d85724 p = 1) : d88456 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6119 q = 1) (hb : d85724 q = 1) : d88451 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6119, d88451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10357 q ha hb
    | true =>
      simp only [d6119, d88451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10349 q ha hb
  have h2 (q : Pattern) (ha : d6120 q = 1) (hb : d85724 q = 1) : d88452 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6120, d88452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6120, d88452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6121 q = 1) (hb : d85724 q = 1) : d88453 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6121, d88453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6121, d88453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6122 q = 1) (hb : d85724 q = 1) : d88454 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6122, d88454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6122, d88454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6123 q = 1) (hb : d85724 q = 1) : d88455 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6123, d88455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6123, d88455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6124 q = 1) (hb : d85724 q = 1) : d88456 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6124, d88456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6124, d88456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10359 (p : Pattern) (ha : d6127 p = 1) (hb : d85724 p = 1) : d88459 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d770 q = 1) (hb : d85723 q = 1) : d88445 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d88445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10356 q ha hb
    | true =>
      simp only [d770, d88445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d771 q = 1) (hb : d85723 q = 1) : d88446 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d88446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d771, d88446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6115 q = 1) (hb : d85724 q = 1) : d88447 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6115, d85724, d88447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6115, d85724, d88447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6116 q = 1) (hb : d85724 q = 1) : d88448 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6116, d88448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6116, d88448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6117 q = 1) (hb : d85724 q = 1) : d88449 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6117, d88449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6117, d88449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6127 q = 1) (hb : d85724 q = 1) : d88459 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6127, d88459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6127, d88459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro10360 (p : Pattern) (ha : d6133 p = 1) (hb : d85724 p = 1) : d88465 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6119 q = 1) (hb : d85724 q = 1) : d88451 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6119, d88451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10357 q ha hb
    | true =>
      simp only [d6119, d88451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10349 q ha hb
  have h2 (q : Pattern) (ha : d6120 q = 1) (hb : d85724 q = 1) : d88452 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6120, d88452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6120, d88452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6121 q = 1) (hb : d85724 q = 1) : d88453 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6121, d88453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6121, d88453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6122 q = 1) (hb : d85724 q = 1) : d88454 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6122, d88454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6122, d88454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6123 q = 1) (hb : d85724 q = 1) : d88455 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6123, d88455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6123, d88455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6128 q = 1) (hb : d85724 q = 1) : d88460 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6128, d88460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10359 q ha hb
    | true =>
      simp only [d6128, d88460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10350 q ha hb
  have h7 (q : Pattern) (ha : d6129 q = 1) (hb : d85724 q = 1) : d88461 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6129, d88461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6129, d88461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6130 q = 1) (hb : d85724 q = 1) : d88462 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6130, d88462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6130, d88462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d6131 q = 1) (hb : d85724 q = 1) : d88463 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6131, d88463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6131, d88463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6132 q = 1) (hb : d85724 q = 1) : d88464 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6132, d88464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6132, d88464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6133 q = 1) (hb : d85724 q = 1) : d88465 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6133, d88465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6133, d88465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro10361 (p : Pattern) (ha : d4919 p = 1) (hb : d85723 p = 1) : d88494 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d766 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d4913 q = 1) : d4913 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d762 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4914 q = 1) (hb : d85721 q = 1) : d88489 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4914, d85721, d88489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d4914, d85721, d88489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d4915 q = 1) (hb : d85721 q = 1) : d88490 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4915, d88490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4915, d88490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4916 q = 1) (hb : d85721 q = 1) : d88491 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4916, d88491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4916, d88491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4917 q = 1) (hb : d85721 q = 1) : d88492 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d4917, d88492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4917, d88492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d4918 q = 1) (hb : d85723 q = 1) : d88493 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d4918, d85723, d88493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d4918, d85723, d88493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d4919 q = 1) (hb : d85723 q = 1) : d88494 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d4919, d88494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4919, d88494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro10362 (p : Pattern) (ha : d4925 p = 1) (hb : d85724 p = 1) : d88500 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4920 q = 1) (hb : d85723 q = 1) : d88495 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d4920, d88495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10361 q ha hb
    | true =>
      simp only [d4920, d88495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4921 q = 1) (hb : d85723 q = 1) : d88496 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d4921, d88496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4921, d88496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4922 q = 1) (hb : d85724 q = 1) : d88497 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4922, d85724, d88497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4922, d85724, d88497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4923 q = 1) (hb : d85724 q = 1) : d88498 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4923, d88498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4923, d88498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d4924 q = 1) (hb : d85724 q = 1) : d88499 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4924, d88499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4924, d88499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d4925 q = 1) (hb : d85724 q = 1) : d88500 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d4925, d88500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4925, d88500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10363 (p : Pattern) (ha : d6193 p = 1) (hb : d85724 p = 1) : d88532 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6188 q = 1) (hb : d85724 q = 1) : d88527 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6188, d88527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10362 q ha hb
    | true =>
      simp only [d6188, d88527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10349 q ha hb
  have h2 (q : Pattern) (ha : d6189 q = 1) (hb : d85724 q = 1) : d88528 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6189, d88528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6189, d88528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6190 q = 1) (hb : d85724 q = 1) : d88529 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6190, d88529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6190, d88529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6191 q = 1) (hb : d85724 q = 1) : d88530 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6191, d88530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6191, d88530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6192 q = 1) (hb : d85724 q = 1) : d88531 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6192, d88531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6192, d88531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d939 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10349 q ha hb
    | true =>
      simp only [d939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d940 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d941 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d942 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d943 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6193 q = 1) (hb : d85724 q = 1) : d88532 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6193, d88532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6193, d88532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro10364 (p : Pattern) (ha : d806 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d774 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10348 q ha hb
    | true =>
      simp only [d774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d775 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d780 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d780, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d781 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d805 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d806 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10365 (p : Pattern) (ha : d816 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d774 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10348 q ha hb
    | true =>
      simp only [d774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d775 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d780 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d780, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d814 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d815 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d816 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10366 (p : Pattern) (ha : d6138 p = 1) (hb : d85724 p = 1) : d88470 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d770 q = 1) (hb : d85723 q = 1) : d88445 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d88445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10356 q ha hb
    | true =>
      simp only [d770, d88445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d771 q = 1) (hb : d85723 q = 1) : d88446 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d88446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d771, d88446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6115 q = 1) (hb : d85724 q = 1) : d88447 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6115, d85724, d88447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6115, d85724, d88447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6116 q = 1) (hb : d85724 q = 1) : d88448 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6116, d88448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6116, d88448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6137 q = 1) (hb : d85724 q = 1) : d88469 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6137, d88469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6137, d88469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6138 q = 1) (hb : d85724 q = 1) : d88470 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6138, d88470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6138, d88470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10367 (p : Pattern) (ha : d6145 p = 1) (hb : d85724 p = 1) : d88477 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d770 q = 1) (hb : d85723 q = 1) : d88445 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d88445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10356 q ha hb
    | true =>
      simp only [d770, d88445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d771 q = 1) (hb : d85723 q = 1) : d88446 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d88446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d771, d88446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6115 q = 1) (hb : d85724 q = 1) : d88447 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6115, d85724, d88447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6115, d85724, d88447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6143 q = 1) (hb : d85724 q = 1) : d88475 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6143, d88475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6143, d88475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6144 q = 1) (hb : d85724 q = 1) : d88476 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6144, d88476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6144, d88476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6145 q = 1) (hb : d85724 q = 1) : d88477 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6145, d88477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6145, d88477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10368 (p : Pattern) (ha : d845 p = 1) (hb : d85723 p = 1) : d88482 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d843 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d756 q = 1) : d756 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d758 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d759 q = 1) (hb : d85721 q = 1) : d11096 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d759, d85721, d11096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d759, d85721, d11096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d760 q = 1) (hb : d85721 q = 1) : d11097 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d760, d11097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d760, d11097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d761 q = 1) (hb : d85721 q = 1) : d11098 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d761, d11098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d761, d11098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d758 q = 1) : d758 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d762 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d763 q = 1) (hb : d85721 q = 1) : d11099 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d85721, d11099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d763, d85721, d11099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d764 q = 1) (hb : d85721 q = 1) : d11100 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d11100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d764, d11100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d765 q = 1) (hb : d85721 q = 1) : d11101 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d11101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d765, d11101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d766 q = 1) (hb : d85721 q = 1) : d11102 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d766, d11102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d766, d11102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d844 q = 1) (hb : d85723 q = 1) : d88481 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d844, d85723, d88481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d844, d85723, d88481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d845 q = 1) (hb : d85723 q = 1) : d88482 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d845, d88482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d845, d88482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro10369 (p : Pattern) (ha : d6152 p = 1) (hb : d85724 p = 1) : d88488 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d846 q = 1) (hb : d85723 q = 1) : d88483 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d846, d88483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10368 q ha hb
    | true =>
      simp only [d846, d88483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d847 q = 1) (hb : d85723 q = 1) : d88484 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d847, d88484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d847, d88484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6149 q = 1) (hb : d85724 q = 1) : d88485 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6149, d85724, d88485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6149, d85724, d88485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6150 q = 1) (hb : d85724 q = 1) : d88486 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6150, d88486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6150, d88486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6151 q = 1) (hb : d85724 q = 1) : d88487 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6151, d88487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6151, d88487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6152 q = 1) (hb : d85724 q = 1) : d88488 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6152, d88488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6152, d88488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10370 (p : Pattern) (ha : d76904 p = 1) (hb : d85724 p = 1) : d88507 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6139 q = 1) (hb : d85724 q = 1) : d88471 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6139, d88471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10366 q ha hb
    | true =>
      simp only [d6139, d88471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10364 q ha hb
  have h2 (q : Pattern) (ha : d6140 q = 1) (hb : d85724 q = 1) : d88472 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6140, d88472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6140, d88472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6141 q = 1) (hb : d85724 q = 1) : d88473 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6141, d88473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6141, d88473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6142 q = 1) (hb : d85724 q = 1) : d88474 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6142, d88474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6142, d88474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6146 q = 1) (hb : d85724 q = 1) : d88478 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6146, d88478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10367 q ha hb
    | true =>
      simp only [d6146, d88478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10365 q ha hb
  have h6 (q : Pattern) (ha : d6147 q = 1) (hb : d85724 q = 1) : d88479 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6147, d88479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6147, d88479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6148 q = 1) (hb : d85724 q = 1) : d88480 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6148, d88480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6148, d88480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6153 q = 1) (hb : d85724 q = 1) : d88501 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6153, d88501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10369 q ha hb
    | true =>
      simp only [d6153, d88501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10362 q ha hb
  have h9 (q : Pattern) (ha : d76900 q = 1) (hb : d85724 q = 1) : d88502 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76900, d88502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76900, d88502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6160 q = 1) (hb : d85724 q = 1) : d88451 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6160, d88451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10357 q ha hb
    | true =>
      simp only [d6160, d88451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d6161 q = 1) (hb : d85724 q = 1) : d88503 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6161, d88503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d6161, d88503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d76901 q = 1) (hb : d85724 q = 1) : d88504 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76901, d88504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76901, d88504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d76902 q = 1) (hb : d85724 q = 1) : d88505 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76902, d88505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d76902, d88505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d76903 q = 1) (hb : d85724 q = 1) : d88506 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76903, d88506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76903, d88506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76904 q = 1) (hb : d85724 q = 1) : d88507 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76904, d88507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76904, d88507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro10371 (p : Pattern) (ha : d916 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d774 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10348 q ha hb
    | true =>
      simp only [d774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d775 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d780 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d780, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d781 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d805 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d916 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro10372 (p : Pattern) (ha : d922 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d774 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10348 q ha hb
    | true =>
      simp only [d774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d775 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d780 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d780, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d814 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d815 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d922 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro10373 (p : Pattern) (ha : d6166 p = 1) (hb : d85724 p = 1) : d88508 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d770 q = 1) (hb : d85723 q = 1) : d88445 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d88445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10356 q ha hb
    | true =>
      simp only [d770, d88445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d771 q = 1) (hb : d85723 q = 1) : d88446 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d88446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d771, d88446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6115 q = 1) (hb : d85724 q = 1) : d88447 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6115, d85724, d88447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6115, d85724, d88447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6116 q = 1) (hb : d85724 q = 1) : d88448 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6116, d88448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6116, d88448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6137 q = 1) (hb : d85724 q = 1) : d88469 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6137, d88469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6137, d88469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6166 q = 1) (hb : d85724 q = 1) : d88508 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6166, d88508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6166, d88508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro10374 (p : Pattern) (ha : d6171 p = 1) (hb : d85724 p = 1) : d88513 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d770 q = 1) (hb : d85723 q = 1) : d88445 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d88445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10356 q ha hb
    | true =>
      simp only [d770, d88445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d771 q = 1) (hb : d85723 q = 1) : d88446 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d88446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d771, d88446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6115 q = 1) (hb : d85724 q = 1) : d88447 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6115, d85724, d88447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6115, d85724, d88447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6143 q = 1) (hb : d85724 q = 1) : d88475 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6143, d88475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6143, d88475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6144 q = 1) (hb : d85724 q = 1) : d88476 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6144, d88476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6144, d88476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6171 q = 1) (hb : d85724 q = 1) : d88513 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6171, d88513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6171, d88513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro10375 (p : Pattern) (ha : d6175 p = 1) (hb : d85724 p = 1) : d88517 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d846 q = 1) (hb : d85723 q = 1) : d88483 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d846, d88483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10368 q ha hb
    | true =>
      simp only [d846, d88483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d847 q = 1) (hb : d85723 q = 1) : d88484 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d847, d88484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d847, d88484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6149 q = 1) (hb : d85724 q = 1) : d88485 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6149, d85724, d88485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6149, d85724, d88485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6150 q = 1) (hb : d85724 q = 1) : d88486 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6150, d88486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6150, d88486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6151 q = 1) (hb : d85724 q = 1) : d88487 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6151, d88487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6151, d88487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6175 q = 1) (hb : d85724 q = 1) : d88517 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6175, d88517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6175, d88517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro10376 (p : Pattern) (ha : d6176 p = 1) (hb : d85724 p = 1) : d88518 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4920 q = 1) (hb : d85723 q = 1) : d88495 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d4920, d88495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10361 q ha hb
    | true =>
      simp only [d4920, d88495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4921 q = 1) (hb : d85723 q = 1) : d88496 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d4921, d88496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4921, d88496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4922 q = 1) (hb : d85724 q = 1) : d88497 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4922, d85724, d88497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4922, d85724, d88497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d4923 q = 1) (hb : d85724 q = 1) : d88498 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4923, d88498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4923, d88498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4924 q = 1) (hb : d85724 q = 1) : d88499 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4924, d88499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4924, d88499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6176 q = 1) (hb : d85724 q = 1) : d88518 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6176, d88518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6176, d88518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro10377 (p : Pattern) (ha : d76909 p = 1) (hb : d85724 p = 1) : d88525 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6139 q = 1) (hb : d85724 q = 1) : d88471 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6139, d88471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10366 q ha hb
    | true =>
      simp only [d6139, d88471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10364 q ha hb
  have h2 (q : Pattern) (ha : d6140 q = 1) (hb : d85724 q = 1) : d88472 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6140, d88472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6140, d88472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6141 q = 1) (hb : d85724 q = 1) : d88473 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6141, d88473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6141, d88473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6142 q = 1) (hb : d85724 q = 1) : d88474 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6142, d88474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6142, d88474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6146 q = 1) (hb : d85724 q = 1) : d88478 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6146, d88478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10367 q ha hb
    | true =>
      simp only [d6146, d88478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10365 q ha hb
  have h6 (q : Pattern) (ha : d6147 q = 1) (hb : d85724 q = 1) : d88479 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6147, d88479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6147, d88479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6148 q = 1) (hb : d85724 q = 1) : d88480 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6148, d88480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6148, d88480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6153 q = 1) (hb : d85724 q = 1) : d88501 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6153, d88501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10369 q ha hb
    | true =>
      simp only [d6153, d88501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10362 q ha hb
  have h9 (q : Pattern) (ha : d76900 q = 1) (hb : d85724 q = 1) : d88502 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76900, d88502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76900, d88502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6160 q = 1) (hb : d85724 q = 1) : d88451 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6160, d88451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10357 q ha hb
    | true =>
      simp only [d6160, d88451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d6161 q = 1) (hb : d85724 q = 1) : d88503 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6161, d88503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d6161, d88503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d76901 q = 1) (hb : d85724 q = 1) : d88504 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76901, d88504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76901, d88504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d76902 q = 1) (hb : d85724 q = 1) : d88505 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76902, d88505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d76902, d88505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d76903 q = 1) (hb : d85724 q = 1) : d88506 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76903, d88506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76903, d88506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d6167 q = 1) (hb : d85724 q = 1) : d88509 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6167, d88509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10373 q ha hb
    | true =>
      simp only [d6167, d88509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10371 q ha hb
  have h16 (q : Pattern) (ha : d6168 q = 1) (hb : d85724 q = 1) : d88510 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6168, d88510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6168, d88510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d6169 q = 1) (hb : d85724 q = 1) : d88511 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6169, d88511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d6169, d88511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d6170 q = 1) (hb : d85724 q = 1) : d88512 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6170, d88512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6170, d88512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d6172 q = 1) (hb : d85724 q = 1) : d88514 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6172, d88514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10374 q ha hb
    | true =>
      simp only [d6172, d88514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10372 q ha hb
  have h20 (q : Pattern) (ha : d6173 q = 1) (hb : d85724 q = 1) : d88515 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6173, d88515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6173, d88515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d6174 q = 1) (hb : d85724 q = 1) : d88516 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6174, d88516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d6174, d88516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d6177 q = 1) (hb : d85724 q = 1) : d88519 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6177, d88519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10375 q ha hb
    | true =>
      simp only [d6177, d88519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10376 q ha hb
  have h23 (q : Pattern) (ha : d76905 q = 1) (hb : d85724 q = 1) : d88520 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76905, d88520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d76905, d88520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d6181 q = 1) (hb : d85724 q = 1) : d88460 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6181, d88460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10359 q ha hb
    | true =>
      simp only [d6181, d88460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d6182 q = 1) (hb : d85724 q = 1) : d88521 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6182, d88521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d6182, d88521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d76906 q = 1) (hb : d85724 q = 1) : d88522 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76906, d88522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d76906, d88522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d76907 q = 1) (hb : d85724 q = 1) : d88523 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76907, d88523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d76907, d88523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d76908 q = 1) (hb : d85724 q = 1) : d88524 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76908, d88524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d76908, d88524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d76909 q = 1) (hb : d85724 q = 1) : d88525 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76909, d88525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d76909, d88525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro10378 (p : Pattern) (ha : d76916 p = 1) (hb : d85724 p = 1) : d88539 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6177 q = 1) (hb : d85724 q = 1) : d88519 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6177, d88519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10375 q ha hb
    | true =>
      simp only [d6177, d88519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10376 q ha hb
  have h2 (q : Pattern) (ha : d76905 q = 1) (hb : d85724 q = 1) : d88520 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76905, d88520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76905, d88520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6181 q = 1) (hb : d85724 q = 1) : d88460 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6181, d88460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10359 q ha hb
    | true =>
      simp only [d6181, d88460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6182 q = 1) (hb : d85724 q = 1) : d88521 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6182, d88521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6182, d88521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d76906 q = 1) (hb : d85724 q = 1) : d88522 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76906, d88522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76906, d88522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76914 q = 1) (hb : d85724 q = 1) : d88537 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76914, d88537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76914, d88537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76915 q = 1) (hb : d85724 q = 1) : d88538 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76915, d88538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76915, d88538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76916 q = 1) (hb : d85724 q = 1) : d88539 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76916, d88539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76916, d88539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10379 (p : Pattern) (ha : d992 p = 1) (hb : d85723 p = 1) : d88546 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d976 q = 1) : d976 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d981 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d982 q = 1) (hb : d85721 q = 1) : d11267 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d982, d85721, d11267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d982, d85721, d11267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d983 q = 1) (hb : d85721 q = 1) : d11268 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d983, d11268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d983, d11268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d984 q = 1) (hb : d85721 q = 1) : d11269 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d984, d11269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d984, d11269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d981 q = 1) : d981 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d986 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d987 q = 1) (hb : d85721 q = 1) : d11271 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d85721, d11271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d987, d85721, d11271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d988 q = 1) (hb : d85721 q = 1) : d11272 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d11272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d988, d11272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d989 q = 1) (hb : d85721 q = 1) : d11273 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d11273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d989, d11273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d990 q = 1) (hb : d85721 q = 1) : d11274 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d990, d11274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d990, d11274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d991 q = 1) (hb : d85723 q = 1) : d88545 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d991, d85723, d88545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d991, d85723, d88545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d992 q = 1) (hb : d85723 q = 1) : d88546 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d992, d88546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d992, d88546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro10380 (p : Pattern) (ha : d6209 p = 1) (hb : d85724 p = 1) : d88552 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d993 q = 1) (hb : d85723 q = 1) : d88547 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d993, d88547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10379 q ha hb
    | true =>
      simp only [d993, d88547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d994 q = 1) (hb : d85723 q = 1) : d88548 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d994, d88548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d994, d88548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6206 q = 1) (hb : d85724 q = 1) : d88549 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6206, d85724, d88549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6206, d85724, d88549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6207 q = 1) (hb : d85724 q = 1) : d88550 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6207, d88550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6207, d88550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6208 q = 1) (hb : d85724 q = 1) : d88551 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6208, d88551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6208, d88551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6209 q = 1) (hb : d85724 q = 1) : d88552 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6209, d88552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6209, d88552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro10381 (p : Pattern) (ha : d6216 p = 1) (hb : d85723 p = 1) : d88558 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d990 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d6210 q = 1) : d6210 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d986 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6211 q = 1) (hb : d85721 q = 1) : d88553 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6211, d85721, d88553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d6211, d85721, d88553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d6212 q = 1) (hb : d85721 q = 1) : d88554 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6212, d88554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6212, d88554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6213 q = 1) (hb : d85721 q = 1) : d88555 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6213, d88555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6213, d88555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6214 q = 1) (hb : d85721 q = 1) : d88556 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6214, d88556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6214, d88556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d6215 q = 1) (hb : d85723 q = 1) : d88557 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6215, d85723, d88557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6215, d85723, d88557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d6216 q = 1) (hb : d85723 q = 1) : d88558 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6216, d88558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6216, d88558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro10382 (p : Pattern) (ha : d6222 p = 1) (hb : d85724 p = 1) : d88564 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6217 q = 1) (hb : d85723 q = 1) : d88559 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6217, d88559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10381 q ha hb
    | true =>
      simp only [d6217, d88559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6218 q = 1) (hb : d85723 q = 1) : d88560 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6218, d88560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6218, d88560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6219 q = 1) (hb : d85724 q = 1) : d88561 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6219, d85724, d88561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6219, d85724, d88561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6220 q = 1) (hb : d85724 q = 1) : d88562 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6220, d88562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6220, d88562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6221 q = 1) (hb : d85724 q = 1) : d88563 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6221, d88563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6221, d88563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6222 q = 1) (hb : d85724 q = 1) : d88564 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6222, d88564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6222, d88564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro10383 (p : Pattern) (ha : d997 p = 1) (hb : d85723 p = 1) : d88568 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d990 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d981 q = 1) : d981 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d986 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d987 q = 1) (hb : d85721 q = 1) : d11271 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d85721, d11271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d987, d85721, d11271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d988 q = 1) (hb : d85721 q = 1) : d11272 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d11272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d988, d11272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d989 q = 1) (hb : d85721 q = 1) : d11273 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d11273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d989, d11273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d995 q = 1) (hb : d85721 q = 1) : d11279 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, d11279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d995, d11279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d996 q = 1) (hb : d85723 q = 1) : d88567 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d996, d85723, d88567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d996, d85723, d88567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d997 q = 1) (hb : d85723 q = 1) : d88568 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d997, d88568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d997, d88568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro10384 (p : Pattern) (ha : d6233 p = 1) (hb : d85724 p = 1) : d88574 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d998 q = 1) (hb : d85723 q = 1) : d88569 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d998, d88569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10383 q ha hb
    | true =>
      simp only [d998, d88569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d999 q = 1) (hb : d85723 q = 1) : d88570 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d999, d88570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d999, d88570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6230 q = 1) (hb : d85724 q = 1) : d88571 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6230, d85724, d88571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6230, d85724, d88571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6231 q = 1) (hb : d85724 q = 1) : d88572 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6231, d88572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6231, d88572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6232 q = 1) (hb : d85724 q = 1) : d88573 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6232, d88573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6232, d88573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6233 q = 1) (hb : d85724 q = 1) : d88574 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6233, d88574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6233, d88574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro10385 (p : Pattern) (ha : d76926 p = 1) (hb : d85724 p = 1) : d88580 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6223 q = 1) (hb : d85724 q = 1) : d88565 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6223, d88565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10380 q ha hb
    | true =>
      simp only [d6223, d88565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10382 q ha hb
  have h2 (q : Pattern) (ha : d76922 q = 1) (hb : d85724 q = 1) : d88566 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76922, d88566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76922, d88566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6234 q = 1) (hb : d85724 q = 1) : d88575 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6234, d88575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10384 q ha hb
    | true =>
      simp only [d6234, d88575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6235 q = 1) (hb : d85724 q = 1) : d88576 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6235, d88576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6235, d88576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d76923 q = 1) (hb : d85724 q = 1) : d88577 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76923, d88577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76923, d88577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76924 q = 1) (hb : d85724 q = 1) : d88578 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76924, d88578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76924, d88578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76925 q = 1) (hb : d85724 q = 1) : d88579 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76925, d88579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76925, d88579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76926 q = 1) (hb : d85724 q = 1) : d88580 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76926, d88580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76926, d88580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10386 (p : Pattern) (ha : d76932 p = 1) (hb : d85724 p = 1) : d88586 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6125 q = 1) (hb : d85724 q = 1) : d88457 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6125, d88457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6125, d88457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10358 q ha hb
  have h2 (q : Pattern) (ha : d6126 q = 1) (hb : d85724 q = 1) : d88458 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6126, d88458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6126, d88458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6134 q = 1) (hb : d85724 q = 1) : d88466 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6134, d88466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10358 q ha hb
    | true =>
      simp only [d6134, d88466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10360 q ha hb
  have h4 (q : Pattern) (ha : d6135 q = 1) (hb : d85724 q = 1) : d88467 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6135, d88467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6135, d88467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6136 q = 1) (hb : d85724 q = 1) : d88468 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d6136, d88468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6136, d88468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76910 q = 1) (hb : d85724 q = 1) : d88526 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76910, d88526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10370 q ha hb
    | true =>
      simp only [d76910, d88526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10377 q ha hb
  have h7 (q : Pattern) (ha : d6194 q = 1) (hb : d85724 q = 1) : d88533 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6194, d88533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10363 q ha hb
    | true =>
      simp only [d6194, d88533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10351 q ha hb
  have h8 (q : Pattern) (ha : d76911 q = 1) (hb : d85724 q = 1) : d88534 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76911, d88534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76911, d88534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76912 q = 1) (hb : d85724 q = 1) : d88535 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76912, d88535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76912, d88535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d76913 q = 1) (hb : d85724 q = 1) : d88536 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76913, d88536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76913, d88536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d76917 q = 1) (hb : d85724 q = 1) : d88540 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76917, d88540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76917, d88540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10378 q ha hb
  have h12 (q : Pattern) (ha : d960 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10352 q ha hb
  have h13 (q : Pattern) (ha : d76918 q = 1) (hb : d85724 q = 1) : d88541 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76918, d88541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76918, d88541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d76919 q = 1) (hb : d85724 q = 1) : d88542 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76919, d88542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76919, d88542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d76920 q = 1) (hb : d85724 q = 1) : d88543 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76920, d88543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d76920, d88543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d76921 q = 1) (hb : d85724 q = 1) : d88544 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76921, d88544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76921, d88544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d76927 q = 1) (hb : d85724 q = 1) : d88581 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76927, d88581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76927, d88581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10385 q ha hb
  have h18 (q : Pattern) (ha : d1070 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10355 q ha hb
  have h19 (q : Pattern) (ha : d76928 q = 1) (hb : d85724 q = 1) : d88582 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76928, d88582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d76928, d88582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d76929 q = 1) (hb : d85724 q = 1) : d88583 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76929, d88583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d76929, d88583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d76930 q = 1) (hb : d85724 q = 1) : d88584 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76930, d88584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d76930, d88584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d76931 q = 1) (hb : d85724 q = 1) : d88585 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76931, d88585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d76931, d88585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d76932 q = 1) (hb : d85724 q = 1) : d88586 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d76932, d88586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d76932, d88586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro10387 (p : Pattern) (ha : d76938 p = 1) (hb : d85724 p = 1) : d88592 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76933 q = 1) (hb : d85724 q = 1) : d88587 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d76933, d88587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76933, d88587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10386 q ha hb
  have h2 (q : Pattern) (ha : d76934 q = 1) (hb : d85724 q = 1) : d88588 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d76934, d88588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76934, d88588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76935 q = 1) (hb : d85724 q = 1) : d88589 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d76935, d88589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76935, d88589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76936 q = 1) (hb : d85724 q = 1) : d88590 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d76936, d88590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76936, d88590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76937 q = 1) (hb : d85724 q = 1) : d88591 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d76937, d88591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76937, d88591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76938 q = 1) (hb : d85724 q = 1) : d88592 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d76938, d88592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76938, d88592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10388 (p : Pattern) (ha : d1152 p = 1) (hb : d85723 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1146 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1151 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1151, d85723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1151, d85723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1152 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro10389 (p : Pattern) (ha : d1162 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1153 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10388 q ha hb
    | true =>
      simp only [d1153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1154 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1159 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1159, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1160 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1161 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1162 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10390 (p : Pattern) (ha : d1172 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10388 q ha hb
    | true =>
      simp only [d1153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1159 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1160 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1161 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d1172 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro10391 (p : Pattern) (ha : d1361 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1350 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10389 q ha hb
    | true =>
      simp only [d1350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1351 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1352 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1353 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1354 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1356 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10390 q ha hb
    | true =>
      simp only [d1356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1357 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1358 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1359 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1360 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1361 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro10392 (p : Pattern) (ha : d1370 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1356 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10390 q ha hb
    | true =>
      simp only [d1356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1357 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1358 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1359 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1360 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1370 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10393 (p : Pattern) (ha : d1430 p = 1) (hb : d85723 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1420 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1429 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1429, d85723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1429, d85723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1430 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro10394 (p : Pattern) (ha : d1497 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1431 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10393 q ha hb
    | true =>
      simp only [d1431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1432 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1494 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1494, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1494, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1495 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1496 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d1497 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro10395 (p : Pattern) (ha : d1503 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1498 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10394 q ha hb
    | true =>
      simp only [d1498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1499 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1500 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1501 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1502 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1503 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10396 (p : Pattern) (ha : d1148 p = 1) (hb : d85723 p = 1) : d88596 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d1128 q = 1) : d1128 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1141 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1142 q = 1) (hb : d85721 q = 1) : d11369 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1142, d85721, d11369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d1142, d85721, d11369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1143 q = 1) (hb : d85721 q = 1) : d11370 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1143, d11370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1143, d11370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1144 q = 1) (hb : d85721 q = 1) : d11371 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1144, d11371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1144, d11371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1146 q = 1) (hb : d85721 q = 1) : d11373 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1146, d11373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1146, d11373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d1147 q = 1) (hb : d85723 q = 1) : d88595 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1147, d85723, d88595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1147, d85723, d88595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d1148 q = 1) (hb : d85723 q = 1) : d88596 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1148, d88596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1148, d88596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro10397 (p : Pattern) (ha : d6257 p = 1) (hb : d85724 p = 1) : d88602 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1149 q = 1) (hb : d85723 q = 1) : d88597 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d88597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10396 q ha hb
    | true =>
      simp only [d1149, d88597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1150 q = 1) (hb : d85723 q = 1) : d88598 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d88598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1150, d88598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6254 q = 1) (hb : d85724 q = 1) : d88599 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6254, d85724, d88599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6254, d85724, d88599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6255 q = 1) (hb : d85724 q = 1) : d88600 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6255, d88600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6255, d88600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6256 q = 1) (hb : d85724 q = 1) : d88601 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6256, d88601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6256, d88601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6257 q = 1) (hb : d85724 q = 1) : d88602 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6257, d88602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6257, d88602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10398 (p : Pattern) (ha : d6263 p = 1) (hb : d85724 p = 1) : d88608 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6258 q = 1) (hb : d85724 q = 1) : d88603 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6258, d88603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10397 q ha hb
    | true =>
      simp only [d6258, d88603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10389 q ha hb
  have h2 (q : Pattern) (ha : d6259 q = 1) (hb : d85724 q = 1) : d88604 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6259, d88604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6259, d88604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6260 q = 1) (hb : d85724 q = 1) : d88605 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6260, d88605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6260, d88605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6261 q = 1) (hb : d85724 q = 1) : d88606 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6261, d88606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6261, d88606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6262 q = 1) (hb : d85724 q = 1) : d88607 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6262, d88607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6262, d88607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6263 q = 1) (hb : d85724 q = 1) : d88608 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6263, d88608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6263, d88608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10399 (p : Pattern) (ha : d6266 p = 1) (hb : d85724 p = 1) : d88611 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1149 q = 1) (hb : d85723 q = 1) : d88597 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d88597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10396 q ha hb
    | true =>
      simp only [d1149, d88597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1150 q = 1) (hb : d85723 q = 1) : d88598 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d88598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1150, d88598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6254 q = 1) (hb : d85724 q = 1) : d88599 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6254, d85724, d88599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6254, d85724, d88599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6255 q = 1) (hb : d85724 q = 1) : d88600 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6255, d88600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6255, d88600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6256 q = 1) (hb : d85724 q = 1) : d88601 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6256, d88601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6256, d88601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6266 q = 1) (hb : d85724 q = 1) : d88611 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6266, d88611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6266, d88611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro10400 (p : Pattern) (ha : d6272 p = 1) (hb : d85724 p = 1) : d88617 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6258 q = 1) (hb : d85724 q = 1) : d88603 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6258, d88603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10397 q ha hb
    | true =>
      simp only [d6258, d88603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10389 q ha hb
  have h2 (q : Pattern) (ha : d6259 q = 1) (hb : d85724 q = 1) : d88604 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6259, d88604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6259, d88604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6260 q = 1) (hb : d85724 q = 1) : d88605 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6260, d88605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6260, d88605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6261 q = 1) (hb : d85724 q = 1) : d88606 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6261, d88606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6261, d88606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6262 q = 1) (hb : d85724 q = 1) : d88607 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6262, d88607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6262, d88607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6267 q = 1) (hb : d85724 q = 1) : d88612 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6267, d88612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10399 q ha hb
    | true =>
      simp only [d6267, d88612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10390 q ha hb
  have h7 (q : Pattern) (ha : d6268 q = 1) (hb : d85724 q = 1) : d88613 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6268, d88613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6268, d88613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6269 q = 1) (hb : d85724 q = 1) : d88614 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6269, d88614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6269, d88614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d6270 q = 1) (hb : d85724 q = 1) : d88615 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6270, d88615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6270, d88615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6271 q = 1) (hb : d85724 q = 1) : d88616 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6271, d88616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6271, d88616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6272 q = 1) (hb : d85724 q = 1) : d88617 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6272, d88617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6272, d88617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro10401 (p : Pattern) (ha : d5029 p = 1) (hb : d85723 p = 1) : d88646 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d5009 q = 1) : d5009 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d5023 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5024 q = 1) (hb : d85721 q = 1) : d88641 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5024, d85721, d88641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d5024, d85721, d88641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d5025 q = 1) (hb : d85721 q = 1) : d88642 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5025, d88642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5025, d88642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5026 q = 1) (hb : d85721 q = 1) : d88643 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5026, d88643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5026, d88643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5027 q = 1) (hb : d85721 q = 1) : d88644 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5027, d88644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5027, d88644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d5028 q = 1) (hb : d85723 q = 1) : d88645 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d5028, d85723, d88645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5028, d85723, d88645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d5029 q = 1) (hb : d85723 q = 1) : d88646 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d5029, d88646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5029, d88646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro10402 (p : Pattern) (ha : d5035 p = 1) (hb : d85724 p = 1) : d88652 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5030 q = 1) (hb : d85723 q = 1) : d88647 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5030, d88647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10401 q ha hb
    | true =>
      simp only [d5030, d88647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5031 q = 1) (hb : d85723 q = 1) : d88648 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5031, d88648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5031, d88648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5032 q = 1) (hb : d85724 q = 1) : d88649 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5032, d85724, d88649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5032, d85724, d88649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5033 q = 1) (hb : d85724 q = 1) : d88650 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5033, d88650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5033, d88650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d5034 q = 1) (hb : d85724 q = 1) : d88651 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5034, d88651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5034, d88651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d5035 q = 1) (hb : d85724 q = 1) : d88652 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5035, d88652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5035, d88652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10403 (p : Pattern) (ha : d6332 p = 1) (hb : d85724 p = 1) : d88684 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6327 q = 1) (hb : d85724 q = 1) : d88679 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6327, d88679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10402 q ha hb
    | true =>
      simp only [d6327, d88679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10389 q ha hb
  have h2 (q : Pattern) (ha : d6328 q = 1) (hb : d85724 q = 1) : d88680 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6328, d88680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6328, d88680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6329 q = 1) (hb : d85724 q = 1) : d88681 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6329, d88681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6329, d88681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6330 q = 1) (hb : d85724 q = 1) : d88682 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6330, d88682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6330, d88682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6331 q = 1) (hb : d85724 q = 1) : d88683 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6331, d88683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6331, d88683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1350 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10389 q ha hb
    | true =>
      simp only [d1350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1351 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1352 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1353 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1354 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6332 q = 1) (hb : d85724 q = 1) : d88684 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6332, d88684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6332, d88684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro10404 (p : Pattern) (ha : d1185 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1153 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10388 q ha hb
    | true =>
      simp only [d1153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1154 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1159 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1159, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1160 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1184 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1185 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10405 (p : Pattern) (ha : d1195 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1153 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10388 q ha hb
    | true =>
      simp only [d1153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1154 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1159 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1159, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1193 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1194 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1195 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10406 (p : Pattern) (ha : d6277 p = 1) (hb : d85724 p = 1) : d88622 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1149 q = 1) (hb : d85723 q = 1) : d88597 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d88597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10396 q ha hb
    | true =>
      simp only [d1149, d88597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1150 q = 1) (hb : d85723 q = 1) : d88598 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d88598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1150, d88598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6254 q = 1) (hb : d85724 q = 1) : d88599 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6254, d85724, d88599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6254, d85724, d88599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6255 q = 1) (hb : d85724 q = 1) : d88600 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6255, d88600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6255, d88600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6276 q = 1) (hb : d85724 q = 1) : d88621 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6276, d88621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6276, d88621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6277 q = 1) (hb : d85724 q = 1) : d88622 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6277, d88622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6277, d88622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10407 (p : Pattern) (ha : d6284 p = 1) (hb : d85724 p = 1) : d88629 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1149 q = 1) (hb : d85723 q = 1) : d88597 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d88597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10396 q ha hb
    | true =>
      simp only [d1149, d88597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1150 q = 1) (hb : d85723 q = 1) : d88598 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d88598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1150, d88598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6254 q = 1) (hb : d85724 q = 1) : d88599 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6254, d85724, d88599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6254, d85724, d88599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6282 q = 1) (hb : d85724 q = 1) : d88627 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6282, d88627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6282, d88627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6283 q = 1) (hb : d85724 q = 1) : d88628 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6283, d88628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6283, d88628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6284 q = 1) (hb : d85724 q = 1) : d88629 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6284, d88629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6284, d88629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10408 (p : Pattern) (ha : d1221 p = 1) (hb : d85723 p = 1) : d88634 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1219 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d1126 q = 1) : d1126 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1128 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1129 q = 1) (hb : d85721 q = 1) : d11366 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1129, d85721, d11366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d1129, d85721, d11366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1130 q = 1) (hb : d85721 q = 1) : d11367 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1130, d11367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1130, d11367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1131 q = 1) (hb : d85721 q = 1) : d11368 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1131, d11368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1131, d11368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d1128 q = 1) : d1128 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1141 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1142 q = 1) (hb : d85721 q = 1) : d11369 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1142, d85721, d11369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d1142, d85721, d11369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d1143 q = 1) (hb : d85721 q = 1) : d11370 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1143, d11370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1143, d11370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1144 q = 1) (hb : d85721 q = 1) : d11371 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1144, d11371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1144, d11371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1145 q = 1) (hb : d85721 q = 1) : d11372 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1145, d11372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1145, d11372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1220 q = 1) (hb : d85723 q = 1) : d88633 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1220, d85723, d88633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1220, d85723, d88633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d1221 q = 1) (hb : d85723 q = 1) : d88634 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1221, d88634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1221, d88634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro10409 (p : Pattern) (ha : d6291 p = 1) (hb : d85724 p = 1) : d88640 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1222 q = 1) (hb : d85723 q = 1) : d88635 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1222, d88635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10408 q ha hb
    | true =>
      simp only [d1222, d88635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1223 q = 1) (hb : d85723 q = 1) : d88636 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1223, d88636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1223, d88636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6288 q = 1) (hb : d85724 q = 1) : d88637 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6288, d85724, d88637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6288, d85724, d88637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6289 q = 1) (hb : d85724 q = 1) : d88638 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6289, d88638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6289, d88638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6290 q = 1) (hb : d85724 q = 1) : d88639 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6290, d88639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6290, d88639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6291 q = 1) (hb : d85724 q = 1) : d88640 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6291, d88640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6291, d88640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10410 (p : Pattern) (ha : d76945 p = 1) (hb : d85724 p = 1) : d88659 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6278 q = 1) (hb : d85724 q = 1) : d88623 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6278, d88623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10406 q ha hb
    | true =>
      simp only [d6278, d88623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10404 q ha hb
  have h2 (q : Pattern) (ha : d6279 q = 1) (hb : d85724 q = 1) : d88624 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6279, d88624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6279, d88624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6280 q = 1) (hb : d85724 q = 1) : d88625 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6280, d88625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6280, d88625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6281 q = 1) (hb : d85724 q = 1) : d88626 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6281, d88626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6281, d88626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6285 q = 1) (hb : d85724 q = 1) : d88630 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6285, d88630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10407 q ha hb
    | true =>
      simp only [d6285, d88630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10405 q ha hb
  have h6 (q : Pattern) (ha : d6286 q = 1) (hb : d85724 q = 1) : d88631 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6286, d88631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6286, d88631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6287 q = 1) (hb : d85724 q = 1) : d88632 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6287, d88632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6287, d88632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6292 q = 1) (hb : d85724 q = 1) : d88653 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6292, d88653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10409 q ha hb
    | true =>
      simp only [d6292, d88653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10402 q ha hb
  have h9 (q : Pattern) (ha : d76941 q = 1) (hb : d85724 q = 1) : d88654 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76941, d88654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76941, d88654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6299 q = 1) (hb : d85724 q = 1) : d88603 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6299, d88603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10397 q ha hb
    | true =>
      simp only [d6299, d88603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d6300 q = 1) (hb : d85724 q = 1) : d88655 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6300, d88655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d6300, d88655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d76942 q = 1) (hb : d85724 q = 1) : d88656 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76942, d88656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76942, d88656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d76943 q = 1) (hb : d85724 q = 1) : d88657 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76943, d88657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d76943, d88657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d76944 q = 1) (hb : d85724 q = 1) : d88658 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76944, d88658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76944, d88658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76945 q = 1) (hb : d85724 q = 1) : d88659 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76945, d88659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76945, d88659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro10411 (p : Pattern) (ha : d1327 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1153 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10388 q ha hb
    | true =>
      simp only [d1153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1154 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1159 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1159, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1160 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1184 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1327 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro10412 (p : Pattern) (ha : d1333 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1153 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10388 q ha hb
    | true =>
      simp only [d1153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1154 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1159 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1159, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1193 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1194 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1333 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro10413 (p : Pattern) (ha : d6305 p = 1) (hb : d85724 p = 1) : d88660 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1149 q = 1) (hb : d85723 q = 1) : d88597 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d88597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10396 q ha hb
    | true =>
      simp only [d1149, d88597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1150 q = 1) (hb : d85723 q = 1) : d88598 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d88598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1150, d88598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6254 q = 1) (hb : d85724 q = 1) : d88599 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6254, d85724, d88599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6254, d85724, d88599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6255 q = 1) (hb : d85724 q = 1) : d88600 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6255, d88600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6255, d88600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6276 q = 1) (hb : d85724 q = 1) : d88621 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6276, d88621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6276, d88621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6305 q = 1) (hb : d85724 q = 1) : d88660 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6305, d88660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6305, d88660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro10414 (p : Pattern) (ha : d6310 p = 1) (hb : d85724 p = 1) : d88665 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1149 q = 1) (hb : d85723 q = 1) : d88597 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d88597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10396 q ha hb
    | true =>
      simp only [d1149, d88597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1150 q = 1) (hb : d85723 q = 1) : d88598 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d88598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1150, d88598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6254 q = 1) (hb : d85724 q = 1) : d88599 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6254, d85724, d88599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6254, d85724, d88599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6282 q = 1) (hb : d85724 q = 1) : d88627 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6282, d88627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6282, d88627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6283 q = 1) (hb : d85724 q = 1) : d88628 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6283, d88628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6283, d88628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6310 q = 1) (hb : d85724 q = 1) : d88665 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6310, d88665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6310, d88665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro10415 (p : Pattern) (ha : d6314 p = 1) (hb : d85724 p = 1) : d88669 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1222 q = 1) (hb : d85723 q = 1) : d88635 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1222, d88635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10408 q ha hb
    | true =>
      simp only [d1222, d88635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1223 q = 1) (hb : d85723 q = 1) : d88636 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1223, d88636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1223, d88636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6288 q = 1) (hb : d85724 q = 1) : d88637 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6288, d85724, d88637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6288, d85724, d88637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6289 q = 1) (hb : d85724 q = 1) : d88638 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6289, d88638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6289, d88638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6290 q = 1) (hb : d85724 q = 1) : d88639 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6290, d88639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6290, d88639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6314 q = 1) (hb : d85724 q = 1) : d88669 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6314, d88669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6314, d88669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro10416 (p : Pattern) (ha : d6315 p = 1) (hb : d85724 p = 1) : d88670 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5030 q = 1) (hb : d85723 q = 1) : d88647 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5030, d88647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10401 q ha hb
    | true =>
      simp only [d5030, d88647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5031 q = 1) (hb : d85723 q = 1) : d88648 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5031, d88648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5031, d88648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5032 q = 1) (hb : d85724 q = 1) : d88649 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5032, d85724, d88649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5032, d85724, d88649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d5033 q = 1) (hb : d85724 q = 1) : d88650 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5033, d88650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5033, d88650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5034 q = 1) (hb : d85724 q = 1) : d88651 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5034, d88651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5034, d88651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6315 q = 1) (hb : d85724 q = 1) : d88670 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6315, d88670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6315, d88670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro10417 (p : Pattern) (ha : d76950 p = 1) (hb : d85724 p = 1) : d88677 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6278 q = 1) (hb : d85724 q = 1) : d88623 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6278, d88623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10406 q ha hb
    | true =>
      simp only [d6278, d88623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10404 q ha hb
  have h2 (q : Pattern) (ha : d6279 q = 1) (hb : d85724 q = 1) : d88624 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6279, d88624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6279, d88624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6280 q = 1) (hb : d85724 q = 1) : d88625 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6280, d88625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6280, d88625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6281 q = 1) (hb : d85724 q = 1) : d88626 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6281, d88626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6281, d88626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6285 q = 1) (hb : d85724 q = 1) : d88630 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6285, d88630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10407 q ha hb
    | true =>
      simp only [d6285, d88630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10405 q ha hb
  have h6 (q : Pattern) (ha : d6286 q = 1) (hb : d85724 q = 1) : d88631 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6286, d88631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6286, d88631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6287 q = 1) (hb : d85724 q = 1) : d88632 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6287, d88632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6287, d88632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6292 q = 1) (hb : d85724 q = 1) : d88653 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6292, d88653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10409 q ha hb
    | true =>
      simp only [d6292, d88653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10402 q ha hb
  have h9 (q : Pattern) (ha : d76941 q = 1) (hb : d85724 q = 1) : d88654 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76941, d88654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76941, d88654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6299 q = 1) (hb : d85724 q = 1) : d88603 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6299, d88603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10397 q ha hb
    | true =>
      simp only [d6299, d88603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d6300 q = 1) (hb : d85724 q = 1) : d88655 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6300, d88655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d6300, d88655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d76942 q = 1) (hb : d85724 q = 1) : d88656 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76942, d88656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76942, d88656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d76943 q = 1) (hb : d85724 q = 1) : d88657 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76943, d88657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d76943, d88657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d76944 q = 1) (hb : d85724 q = 1) : d88658 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76944, d88658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76944, d88658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d6306 q = 1) (hb : d85724 q = 1) : d88661 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6306, d88661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10413 q ha hb
    | true =>
      simp only [d6306, d88661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10411 q ha hb
  have h16 (q : Pattern) (ha : d6307 q = 1) (hb : d85724 q = 1) : d88662 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6307, d88662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6307, d88662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d6308 q = 1) (hb : d85724 q = 1) : d88663 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6308, d88663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d6308, d88663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d6309 q = 1) (hb : d85724 q = 1) : d88664 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6309, d88664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6309, d88664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d6311 q = 1) (hb : d85724 q = 1) : d88666 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6311, d88666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10414 q ha hb
    | true =>
      simp only [d6311, d88666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10412 q ha hb
  have h20 (q : Pattern) (ha : d6312 q = 1) (hb : d85724 q = 1) : d88667 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6312, d88667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6312, d88667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d6313 q = 1) (hb : d85724 q = 1) : d88668 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6313, d88668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d6313, d88668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d6316 q = 1) (hb : d85724 q = 1) : d88671 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6316, d88671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10415 q ha hb
    | true =>
      simp only [d6316, d88671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10416 q ha hb
  have h23 (q : Pattern) (ha : d76946 q = 1) (hb : d85724 q = 1) : d88672 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76946, d88672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d76946, d88672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d6320 q = 1) (hb : d85724 q = 1) : d88612 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6320, d88612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10399 q ha hb
    | true =>
      simp only [d6320, d88612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d6321 q = 1) (hb : d85724 q = 1) : d88673 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6321, d88673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d6321, d88673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d76947 q = 1) (hb : d85724 q = 1) : d88674 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76947, d88674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d76947, d88674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d76948 q = 1) (hb : d85724 q = 1) : d88675 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76948, d88675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d76948, d88675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d76949 q = 1) (hb : d85724 q = 1) : d88676 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76949, d88676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d76949, d88676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d76950 q = 1) (hb : d85724 q = 1) : d88677 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76950, d88677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d76950, d88677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro10418 (p : Pattern) (ha : d76957 p = 1) (hb : d85724 p = 1) : d88691 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6316 q = 1) (hb : d85724 q = 1) : d88671 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6316, d88671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10415 q ha hb
    | true =>
      simp only [d6316, d88671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10416 q ha hb
  have h2 (q : Pattern) (ha : d76946 q = 1) (hb : d85724 q = 1) : d88672 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76946, d88672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76946, d88672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6320 q = 1) (hb : d85724 q = 1) : d88612 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6320, d88612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10399 q ha hb
    | true =>
      simp only [d6320, d88612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6321 q = 1) (hb : d85724 q = 1) : d88673 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6321, d88673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6321, d88673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d76947 q = 1) (hb : d85724 q = 1) : d88674 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76947, d88674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76947, d88674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76955 q = 1) (hb : d85724 q = 1) : d88689 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76955, d88689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76955, d88689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76956 q = 1) (hb : d85724 q = 1) : d88690 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76956, d88690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76956, d88690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76957 q = 1) (hb : d85724 q = 1) : d88691 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76957, d88691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76957, d88691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10419 (p : Pattern) (ha : d1417 p = 1) (hb : d85723 p = 1) : d88698 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1405 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d1396 q = 1) : d1396 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1401 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1402 q = 1) (hb : d85721 q = 1) : d11537 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1402, d85721, d11537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d1402, d85721, d11537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1403 q = 1) (hb : d85721 q = 1) : d11538 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1403, d11538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1403, d11538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1404 q = 1) (hb : d85721 q = 1) : d11539 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1404, d11539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1404, d11539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d1401 q = 1) : d1401 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1411 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1412 q = 1) (hb : d85721 q = 1) : d11541 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1412, d85721, d11541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d1412, d85721, d11541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d1413 q = 1) (hb : d85721 q = 1) : d11542 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1413, d11542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1413, d11542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1414 q = 1) (hb : d85721 q = 1) : d11543 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1414, d11543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1414, d11543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1415 q = 1) (hb : d85721 q = 1) : d11544 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1415, d11544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1415, d11544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1416 q = 1) (hb : d85723 q = 1) : d88697 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1416, d85723, d88697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1416, d85723, d88697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d1417 q = 1) (hb : d85723 q = 1) : d88698 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1417, d88698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1417, d88698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro10420 (p : Pattern) (ha : d6348 p = 1) (hb : d85724 p = 1) : d88704 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1418 q = 1) (hb : d85723 q = 1) : d88699 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1418, d88699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10419 q ha hb
    | true =>
      simp only [d1418, d88699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1419 q = 1) (hb : d85723 q = 1) : d88700 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1419, d88700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1419, d88700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6345 q = 1) (hb : d85724 q = 1) : d88701 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6345, d85724, d88701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6345, d85724, d88701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6346 q = 1) (hb : d85724 q = 1) : d88702 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6346, d88702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6346, d88702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6347 q = 1) (hb : d85724 q = 1) : d88703 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6347, d88703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6347, d88703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6348 q = 1) (hb : d85724 q = 1) : d88704 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6348, d88704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6348, d88704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro10421 (p : Pattern) (ha : d6361 p = 1) (hb : d85723 p = 1) : d88710 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1415 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d6349 q = 1) : d6349 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6355 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6356 q = 1) (hb : d85721 q = 1) : d88705 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6356, d85721, d88705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d6356, d85721, d88705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d6357 q = 1) (hb : d85721 q = 1) : d88706 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6357, d88706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6357, d88706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6358 q = 1) (hb : d85721 q = 1) : d88707 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6358, d88707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6358, d88707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6359 q = 1) (hb : d85721 q = 1) : d88708 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6359, d88708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6359, d88708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d6360 q = 1) (hb : d85723 q = 1) : d88709 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6360, d85723, d88709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6360, d85723, d88709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d6361 q = 1) (hb : d85723 q = 1) : d88710 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6361, d88710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6361, d88710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro10422 (p : Pattern) (ha : d6367 p = 1) (hb : d85724 p = 1) : d88716 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6362 q = 1) (hb : d85723 q = 1) : d88711 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6362, d88711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10421 q ha hb
    | true =>
      simp only [d6362, d88711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6363 q = 1) (hb : d85723 q = 1) : d88712 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6363, d88712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6363, d88712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6364 q = 1) (hb : d85724 q = 1) : d88713 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6364, d85724, d88713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6364, d85724, d88713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6365 q = 1) (hb : d85724 q = 1) : d88714 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6365, d88714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6365, d88714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6366 q = 1) (hb : d85724 q = 1) : d88715 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6366, d88715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6366, d88715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6367 q = 1) (hb : d85724 q = 1) : d88716 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6367, d88716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6367, d88716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro10423 (p : Pattern) (ha : d1422 p = 1) (hb : d85723 p = 1) : d88720 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1415 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d1401 q = 1) : d1401 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1411 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1412 q = 1) (hb : d85721 q = 1) : d11541 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1412, d85721, d11541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d1412, d85721, d11541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1413 q = 1) (hb : d85721 q = 1) : d11542 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1413, d11542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1413, d11542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1414 q = 1) (hb : d85721 q = 1) : d11543 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1414, d11543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1414, d11543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1420 q = 1) (hb : d85721 q = 1) : d11549 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1420, d11549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1420, d11549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d1421 q = 1) (hb : d85723 q = 1) : d88719 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1421, d85723, d88719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1421, d85723, d88719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d1422 q = 1) (hb : d85723 q = 1) : d88720 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1422, d88720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1422, d88720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro10424 (p : Pattern) (ha : d6378 p = 1) (hb : d85724 p = 1) : d88726 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1423 q = 1) (hb : d85723 q = 1) : d88721 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1423, d88721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10423 q ha hb
    | true =>
      simp only [d1423, d88721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1424 q = 1) (hb : d85723 q = 1) : d88722 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1424, d88722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1424, d88722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6375 q = 1) (hb : d85724 q = 1) : d88723 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6375, d85724, d88723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6375, d85724, d88723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6376 q = 1) (hb : d85724 q = 1) : d88724 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6376, d88724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6376, d88724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6377 q = 1) (hb : d85724 q = 1) : d88725 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6377, d88725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6377, d88725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6378 q = 1) (hb : d85724 q = 1) : d88726 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6378, d88726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6378, d88726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro10425 (p : Pattern) (ha : d76967 p = 1) (hb : d85724 p = 1) : d88732 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6368 q = 1) (hb : d85724 q = 1) : d88717 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6368, d88717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10420 q ha hb
    | true =>
      simp only [d6368, d88717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10422 q ha hb
  have h2 (q : Pattern) (ha : d76963 q = 1) (hb : d85724 q = 1) : d88718 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76963, d88718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76963, d88718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6379 q = 1) (hb : d85724 q = 1) : d88727 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6379, d88727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10424 q ha hb
    | true =>
      simp only [d6379, d88727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6380 q = 1) (hb : d85724 q = 1) : d88728 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6380, d88728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6380, d88728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d76964 q = 1) (hb : d85724 q = 1) : d88729 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76964, d88729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76964, d88729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76965 q = 1) (hb : d85724 q = 1) : d88730 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76965, d88730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76965, d88730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76966 q = 1) (hb : d85724 q = 1) : d88731 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76966, d88731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76966, d88731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76967 q = 1) (hb : d85724 q = 1) : d88732 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76967, d88732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76967, d88732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10426 (p : Pattern) (ha : d76973 p = 1) (hb : d85724 p = 1) : d88738 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6264 q = 1) (hb : d85724 q = 1) : d88609 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6264, d88609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6264, d88609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10398 q ha hb
  have h2 (q : Pattern) (ha : d6265 q = 1) (hb : d85724 q = 1) : d88610 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6265, d88610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6265, d88610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6273 q = 1) (hb : d85724 q = 1) : d88618 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6273, d88618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10398 q ha hb
    | true =>
      simp only [d6273, d88618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10400 q ha hb
  have h4 (q : Pattern) (ha : d6274 q = 1) (hb : d85724 q = 1) : d88619 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6274, d88619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6274, d88619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6275 q = 1) (hb : d85724 q = 1) : d88620 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d6275, d88620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6275, d88620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76951 q = 1) (hb : d85724 q = 1) : d88678 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76951, d88678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10410 q ha hb
    | true =>
      simp only [d76951, d88678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10417 q ha hb
  have h7 (q : Pattern) (ha : d6333 q = 1) (hb : d85724 q = 1) : d88685 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6333, d88685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10403 q ha hb
    | true =>
      simp only [d6333, d88685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10391 q ha hb
  have h8 (q : Pattern) (ha : d76952 q = 1) (hb : d85724 q = 1) : d88686 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76952, d88686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76952, d88686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76953 q = 1) (hb : d85724 q = 1) : d88687 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76953, d88687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76953, d88687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d76954 q = 1) (hb : d85724 q = 1) : d88688 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76954, d88688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76954, d88688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d76958 q = 1) (hb : d85724 q = 1) : d88692 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76958, d88692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76958, d88692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10418 q ha hb
  have h12 (q : Pattern) (ha : d1371 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10392 q ha hb
  have h13 (q : Pattern) (ha : d76959 q = 1) (hb : d85724 q = 1) : d88693 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76959, d88693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76959, d88693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d76960 q = 1) (hb : d85724 q = 1) : d88694 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76960, d88694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76960, d88694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d76961 q = 1) (hb : d85724 q = 1) : d88695 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76961, d88695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d76961, d88695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d76962 q = 1) (hb : d85724 q = 1) : d88696 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76962, d88696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76962, d88696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d76968 q = 1) (hb : d85724 q = 1) : d88733 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76968, d88733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76968, d88733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10425 q ha hb
  have h18 (q : Pattern) (ha : d1504 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10395 q ha hb
  have h19 (q : Pattern) (ha : d76969 q = 1) (hb : d85724 q = 1) : d88734 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76969, d88734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d76969, d88734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d76970 q = 1) (hb : d85724 q = 1) : d88735 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76970, d88735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d76970, d88735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d76971 q = 1) (hb : d85724 q = 1) : d88736 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76971, d88736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d76971, d88736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d76972 q = 1) (hb : d85724 q = 1) : d88737 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76972, d88737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d76972, d88737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d76973 q = 1) (hb : d85724 q = 1) : d88738 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d76973, d88738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d76973, d88738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro10427 (p : Pattern) (ha : d76979 p = 1) (hb : d85724 p = 1) : d88744 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76974 q = 1) (hb : d85724 q = 1) : d88739 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d76974, d88739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76974, d88739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10426 q ha hb
  have h2 (q : Pattern) (ha : d76975 q = 1) (hb : d85724 q = 1) : d88740 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d76975, d88740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76975, d88740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76976 q = 1) (hb : d85724 q = 1) : d88741 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d76976, d88741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76976, d88741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76977 q = 1) (hb : d85724 q = 1) : d88742 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d76977, d88742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76977, d88742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76978 q = 1) (hb : d85724 q = 1) : d88743 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d76978, d88743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76978, d88743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76979 q = 1) (hb : d85724 q = 1) : d88744 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d76979, d88744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76979, d88744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10428 (p : Pattern) (ha : d1613 p = 1) (hb : d85723 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1607 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1612 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1612, d85723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1612, d85723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1613 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro10429 (p : Pattern) (ha : d1623 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1614 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10428 q ha hb
    | true =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1615 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1620 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1620, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1621 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1622 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1623 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10430 (p : Pattern) (ha : d1633 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10428 q ha hb
    | true =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1620 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1621 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1622 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d1633 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro10431 (p : Pattern) (ha : d1838 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1827 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10429 q ha hb
    | true =>
      simp only [d1827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1828 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1829 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1830 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1831 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1833 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10430 q ha hb
    | true =>
      simp only [d1833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1834 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1835 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1836 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1837 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1838 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro10432 (p : Pattern) (ha : d1847 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1833 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10430 q ha hb
    | true =>
      simp only [d1833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1834 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1835 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1836 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1837 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1847 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10433 (p : Pattern) (ha : d1907 p = 1) (hb : d85723 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1897 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1906 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1906, d85723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1906, d85723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1907 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro10434 (p : Pattern) (ha : d1974 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1908 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10433 q ha hb
    | true =>
      simp only [d1908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1909 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1971 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1971, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1971, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1972 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1973 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d1974 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro10435 (p : Pattern) (ha : d1980 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1975 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10434 q ha hb
    | true =>
      simp only [d1975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1976 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1977 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1978 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1979 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1980 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10436 (p : Pattern) (ha : d1609 p = 1) (hb : d85723 p = 1) : d88749 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1606 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d1589 q = 1) : d1589 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1602 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1603 q = 1) (hb : d85721 q = 1) : d11640 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1603, d85721, d11640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d1603, d85721, d11640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1604 q = 1) (hb : d85721 q = 1) : d11641 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1604, d11641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1604, d11641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1605 q = 1) (hb : d85721 q = 1) : d11642 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1605, d11642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1605, d11642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1607 q = 1) (hb : d85721 q = 1) : d11644 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1607, d11644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1607, d11644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d1608 q = 1) (hb : d85723 q = 1) : d88748 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1608, d85723, d88748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1608, d85723, d88748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d1609 q = 1) (hb : d85723 q = 1) : d88749 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1609, d88749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1609, d88749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro10437 (p : Pattern) (ha : d6403 p = 1) (hb : d85724 p = 1) : d88755 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1610 q = 1) (hb : d85723 q = 1) : d88750 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d88750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10436 q ha hb
    | true =>
      simp only [d1610, d88750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1611 q = 1) (hb : d85723 q = 1) : d88751 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d88751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1611, d88751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6400 q = 1) (hb : d85724 q = 1) : d88752 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6400, d85724, d88752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6400, d85724, d88752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6401 q = 1) (hb : d85724 q = 1) : d88753 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6401, d88753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6401, d88753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6402 q = 1) (hb : d85724 q = 1) : d88754 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6402, d88754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6402, d88754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6403 q = 1) (hb : d85724 q = 1) : d88755 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6403, d88755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6403, d88755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10438 (p : Pattern) (ha : d6409 p = 1) (hb : d85724 p = 1) : d88761 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6404 q = 1) (hb : d85724 q = 1) : d88756 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6404, d88756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10437 q ha hb
    | true =>
      simp only [d6404, d88756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10429 q ha hb
  have h2 (q : Pattern) (ha : d6405 q = 1) (hb : d85724 q = 1) : d88757 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6405, d88757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6405, d88757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6406 q = 1) (hb : d85724 q = 1) : d88758 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6406, d88758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6406, d88758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6407 q = 1) (hb : d85724 q = 1) : d88759 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6407, d88759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6407, d88759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6408 q = 1) (hb : d85724 q = 1) : d88760 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6408, d88760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6408, d88760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6409 q = 1) (hb : d85724 q = 1) : d88761 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6409, d88761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6409, d88761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10439 (p : Pattern) (ha : d6412 p = 1) (hb : d85724 p = 1) : d88764 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1610 q = 1) (hb : d85723 q = 1) : d88750 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d88750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10436 q ha hb
    | true =>
      simp only [d1610, d88750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1611 q = 1) (hb : d85723 q = 1) : d88751 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d88751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1611, d88751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6400 q = 1) (hb : d85724 q = 1) : d88752 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6400, d85724, d88752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6400, d85724, d88752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6401 q = 1) (hb : d85724 q = 1) : d88753 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6401, d88753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6401, d88753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6402 q = 1) (hb : d85724 q = 1) : d88754 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6402, d88754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6402, d88754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6412 q = 1) (hb : d85724 q = 1) : d88764 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6412, d88764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6412, d88764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro10440 (p : Pattern) (ha : d6418 p = 1) (hb : d85724 p = 1) : d88770 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6404 q = 1) (hb : d85724 q = 1) : d88756 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6404, d88756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10437 q ha hb
    | true =>
      simp only [d6404, d88756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10429 q ha hb
  have h2 (q : Pattern) (ha : d6405 q = 1) (hb : d85724 q = 1) : d88757 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6405, d88757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6405, d88757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6406 q = 1) (hb : d85724 q = 1) : d88758 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6406, d88758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6406, d88758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6407 q = 1) (hb : d85724 q = 1) : d88759 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6407, d88759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6407, d88759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6408 q = 1) (hb : d85724 q = 1) : d88760 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6408, d88760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6408, d88760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6413 q = 1) (hb : d85724 q = 1) : d88765 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6413, d88765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10439 q ha hb
    | true =>
      simp only [d6413, d88765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10430 q ha hb
  have h7 (q : Pattern) (ha : d6414 q = 1) (hb : d85724 q = 1) : d88766 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6414, d88766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6414, d88766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6415 q = 1) (hb : d85724 q = 1) : d88767 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6415, d88767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6415, d88767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d6416 q = 1) (hb : d85724 q = 1) : d88768 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6416, d88768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6416, d88768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6417 q = 1) (hb : d85724 q = 1) : d88769 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6417, d88769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6417, d88769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6418 q = 1) (hb : d85724 q = 1) : d88770 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6418, d88770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6418, d88770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro10441 (p : Pattern) (ha : d5145 p = 1) (hb : d85723 p = 1) : d88799 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1606 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d5120 q = 1) : d5120 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d5139 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5140 q = 1) (hb : d85721 q = 1) : d88794 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5140, d85721, d88794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d5140, d85721, d88794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d5141 q = 1) (hb : d85721 q = 1) : d88795 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5141, d88795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5141, d88795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5142 q = 1) (hb : d85721 q = 1) : d88796 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5142, d88796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5142, d88796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5143 q = 1) (hb : d85721 q = 1) : d88797 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5143, d88797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5143, d88797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d5144 q = 1) (hb : d85723 q = 1) : d88798 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d5144, d85723, d88798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5144, d85723, d88798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d5145 q = 1) (hb : d85723 q = 1) : d88799 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d5145, d88799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5145, d88799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro10442 (p : Pattern) (ha : d5151 p = 1) (hb : d85724 p = 1) : d88805 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5146 q = 1) (hb : d85723 q = 1) : d88800 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5146, d88800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10441 q ha hb
    | true =>
      simp only [d5146, d88800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5147 q = 1) (hb : d85723 q = 1) : d88801 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5147, d88801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5147, d88801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5148 q = 1) (hb : d85724 q = 1) : d88802 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5148, d85724, d88802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5148, d85724, d88802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5149 q = 1) (hb : d85724 q = 1) : d88803 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5149, d88803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5149, d88803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d5150 q = 1) (hb : d85724 q = 1) : d88804 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5150, d88804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5150, d88804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d5151 q = 1) (hb : d85724 q = 1) : d88805 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5151, d88805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5151, d88805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10443 (p : Pattern) (ha : d6478 p = 1) (hb : d85724 p = 1) : d88837 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6473 q = 1) (hb : d85724 q = 1) : d88832 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6473, d88832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10442 q ha hb
    | true =>
      simp only [d6473, d88832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10429 q ha hb
  have h2 (q : Pattern) (ha : d6474 q = 1) (hb : d85724 q = 1) : d88833 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6474, d88833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6474, d88833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6475 q = 1) (hb : d85724 q = 1) : d88834 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6475, d88834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6475, d88834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6476 q = 1) (hb : d85724 q = 1) : d88835 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6476, d88835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6476, d88835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6477 q = 1) (hb : d85724 q = 1) : d88836 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6477, d88836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6477, d88836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1827 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10429 q ha hb
    | true =>
      simp only [d1827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1828 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1829 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1830 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1831 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6478 q = 1) (hb : d85724 q = 1) : d88837 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6478, d88837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6478, d88837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro10444 (p : Pattern) (ha : d1646 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1614 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10428 q ha hb
    | true =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1615 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1620 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1620, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1621 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1645 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1646 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10445 (p : Pattern) (ha : d1656 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1614 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10428 q ha hb
    | true =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1615 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1620 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1620, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1654 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1655 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1656 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10446 (p : Pattern) (ha : d6423 p = 1) (hb : d85724 p = 1) : d88775 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1610 q = 1) (hb : d85723 q = 1) : d88750 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d88750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10436 q ha hb
    | true =>
      simp only [d1610, d88750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1611 q = 1) (hb : d85723 q = 1) : d88751 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d88751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1611, d88751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6400 q = 1) (hb : d85724 q = 1) : d88752 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6400, d85724, d88752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6400, d85724, d88752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6401 q = 1) (hb : d85724 q = 1) : d88753 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6401, d88753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6401, d88753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6422 q = 1) (hb : d85724 q = 1) : d88774 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6422, d88774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6422, d88774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6423 q = 1) (hb : d85724 q = 1) : d88775 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6423, d88775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6423, d88775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10447 (p : Pattern) (ha : d6430 p = 1) (hb : d85724 p = 1) : d88782 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1610 q = 1) (hb : d85723 q = 1) : d88750 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d88750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10436 q ha hb
    | true =>
      simp only [d1610, d88750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1611 q = 1) (hb : d85723 q = 1) : d88751 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d88751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1611, d88751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6400 q = 1) (hb : d85724 q = 1) : d88752 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6400, d85724, d88752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6400, d85724, d88752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6428 q = 1) (hb : d85724 q = 1) : d88780 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6428, d88780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6428, d88780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6429 q = 1) (hb : d85724 q = 1) : d88781 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6429, d88781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6429, d88781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6430 q = 1) (hb : d85724 q = 1) : d88782 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6430, d88782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6430, d88782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10448 (p : Pattern) (ha : d1676 p = 1) (hb : d85723 p = 1) : d88787 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1674 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d1587 q = 1) : d1587 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1589 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1590 q = 1) (hb : d85721 q = 1) : d11637 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1590, d85721, d11637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d1590, d85721, d11637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1591 q = 1) (hb : d85721 q = 1) : d11638 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1591, d11638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1591, d11638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1592 q = 1) (hb : d85721 q = 1) : d11639 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1592, d11639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1592, d11639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d1589 q = 1) : d1589 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1602 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1603 q = 1) (hb : d85721 q = 1) : d11640 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1603, d85721, d11640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d1603, d85721, d11640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d1604 q = 1) (hb : d85721 q = 1) : d11641 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1604, d11641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1604, d11641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1605 q = 1) (hb : d85721 q = 1) : d11642 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1605, d11642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1605, d11642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1606 q = 1) (hb : d85721 q = 1) : d11643 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1606, d11643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1606, d11643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1675 q = 1) (hb : d85723 q = 1) : d88786 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1675, d85723, d88786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1675, d85723, d88786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d1676 q = 1) (hb : d85723 q = 1) : d88787 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1676, d88787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1676, d88787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro10449 (p : Pattern) (ha : d6437 p = 1) (hb : d85724 p = 1) : d88793 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1677 q = 1) (hb : d85723 q = 1) : d88788 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1677, d88788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10448 q ha hb
    | true =>
      simp only [d1677, d88788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1678 q = 1) (hb : d85723 q = 1) : d88789 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1678, d88789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1678, d88789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6434 q = 1) (hb : d85724 q = 1) : d88790 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6434, d85724, d88790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6434, d85724, d88790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6435 q = 1) (hb : d85724 q = 1) : d88791 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6435, d88791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6435, d88791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6436 q = 1) (hb : d85724 q = 1) : d88792 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6436, d88792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6436, d88792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6437 q = 1) (hb : d85724 q = 1) : d88793 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6437, d88793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6437, d88793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10450 (p : Pattern) (ha : d76987 p = 1) (hb : d85724 p = 1) : d88812 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6424 q = 1) (hb : d85724 q = 1) : d88776 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6424, d88776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10446 q ha hb
    | true =>
      simp only [d6424, d88776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10444 q ha hb
  have h2 (q : Pattern) (ha : d6425 q = 1) (hb : d85724 q = 1) : d88777 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6425, d88777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6425, d88777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6426 q = 1) (hb : d85724 q = 1) : d88778 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6426, d88778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6426, d88778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6427 q = 1) (hb : d85724 q = 1) : d88779 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6427, d88779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6427, d88779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6431 q = 1) (hb : d85724 q = 1) : d88783 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6431, d88783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10447 q ha hb
    | true =>
      simp only [d6431, d88783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10445 q ha hb
  have h6 (q : Pattern) (ha : d6432 q = 1) (hb : d85724 q = 1) : d88784 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6432, d88784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6432, d88784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6433 q = 1) (hb : d85724 q = 1) : d88785 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6433, d88785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6433, d88785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6438 q = 1) (hb : d85724 q = 1) : d88806 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6438, d88806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10449 q ha hb
    | true =>
      simp only [d6438, d88806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10442 q ha hb
  have h9 (q : Pattern) (ha : d76983 q = 1) (hb : d85724 q = 1) : d88807 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76983, d88807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76983, d88807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6445 q = 1) (hb : d85724 q = 1) : d88756 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6445, d88756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10437 q ha hb
    | true =>
      simp only [d6445, d88756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d6446 q = 1) (hb : d85724 q = 1) : d88808 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6446, d88808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d6446, d88808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d76984 q = 1) (hb : d85724 q = 1) : d88809 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76984, d88809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76984, d88809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d76985 q = 1) (hb : d85724 q = 1) : d88810 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76985, d88810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d76985, d88810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d76986 q = 1) (hb : d85724 q = 1) : d88811 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76986, d88811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76986, d88811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76987 q = 1) (hb : d85724 q = 1) : d88812 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76987, d88812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76987, d88812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro10451 (p : Pattern) (ha : d1804 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1614 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10428 q ha hb
    | true =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1615 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1620 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1620, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1621 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1645 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1804 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro10452 (p : Pattern) (ha : d1810 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1614 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10428 q ha hb
    | true =>
      simp only [d1614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1615 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1620 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1620, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1654 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1655 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1810 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro10453 (p : Pattern) (ha : d6451 p = 1) (hb : d85724 p = 1) : d88813 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1610 q = 1) (hb : d85723 q = 1) : d88750 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d88750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10436 q ha hb
    | true =>
      simp only [d1610, d88750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1611 q = 1) (hb : d85723 q = 1) : d88751 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d88751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1611, d88751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6400 q = 1) (hb : d85724 q = 1) : d88752 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6400, d85724, d88752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6400, d85724, d88752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6401 q = 1) (hb : d85724 q = 1) : d88753 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6401, d88753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6401, d88753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6422 q = 1) (hb : d85724 q = 1) : d88774 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6422, d88774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6422, d88774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6451 q = 1) (hb : d85724 q = 1) : d88813 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6451, d88813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6451, d88813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro10454 (p : Pattern) (ha : d6456 p = 1) (hb : d85724 p = 1) : d88818 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1610 q = 1) (hb : d85723 q = 1) : d88750 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d88750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10436 q ha hb
    | true =>
      simp only [d1610, d88750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1611 q = 1) (hb : d85723 q = 1) : d88751 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d88751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1611, d88751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6400 q = 1) (hb : d85724 q = 1) : d88752 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6400, d85724, d88752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6400, d85724, d88752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6428 q = 1) (hb : d85724 q = 1) : d88780 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6428, d88780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6428, d88780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6429 q = 1) (hb : d85724 q = 1) : d88781 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6429, d88781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6429, d88781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6456 q = 1) (hb : d85724 q = 1) : d88818 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6456, d88818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6456, d88818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro10455 (p : Pattern) (ha : d6460 p = 1) (hb : d85724 p = 1) : d88822 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1677 q = 1) (hb : d85723 q = 1) : d88788 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1677, d88788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10448 q ha hb
    | true =>
      simp only [d1677, d88788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1678 q = 1) (hb : d85723 q = 1) : d88789 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1678, d88789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1678, d88789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6434 q = 1) (hb : d85724 q = 1) : d88790 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6434, d85724, d88790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6434, d85724, d88790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6435 q = 1) (hb : d85724 q = 1) : d88791 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6435, d88791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6435, d88791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6436 q = 1) (hb : d85724 q = 1) : d88792 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6436, d88792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6436, d88792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6460 q = 1) (hb : d85724 q = 1) : d88822 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6460, d88822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6460, d88822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro10456 (p : Pattern) (ha : d6461 p = 1) (hb : d85724 p = 1) : d88823 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5146 q = 1) (hb : d85723 q = 1) : d88800 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5146, d88800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10441 q ha hb
    | true =>
      simp only [d5146, d88800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5147 q = 1) (hb : d85723 q = 1) : d88801 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5147, d88801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5147, d88801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5148 q = 1) (hb : d85724 q = 1) : d88802 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5148, d85724, d88802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5148, d85724, d88802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d5149 q = 1) (hb : d85724 q = 1) : d88803 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5149, d88803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5149, d88803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5150 q = 1) (hb : d85724 q = 1) : d88804 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5150, d88804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5150, d88804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6461 q = 1) (hb : d85724 q = 1) : d88823 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6461, d88823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6461, d88823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro10457 (p : Pattern) (ha : d76992 p = 1) (hb : d85724 p = 1) : d88830 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6424 q = 1) (hb : d85724 q = 1) : d88776 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6424, d88776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10446 q ha hb
    | true =>
      simp only [d6424, d88776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10444 q ha hb
  have h2 (q : Pattern) (ha : d6425 q = 1) (hb : d85724 q = 1) : d88777 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6425, d88777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6425, d88777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6426 q = 1) (hb : d85724 q = 1) : d88778 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6426, d88778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6426, d88778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6427 q = 1) (hb : d85724 q = 1) : d88779 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6427, d88779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6427, d88779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6431 q = 1) (hb : d85724 q = 1) : d88783 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6431, d88783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10447 q ha hb
    | true =>
      simp only [d6431, d88783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10445 q ha hb
  have h6 (q : Pattern) (ha : d6432 q = 1) (hb : d85724 q = 1) : d88784 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6432, d88784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6432, d88784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6433 q = 1) (hb : d85724 q = 1) : d88785 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6433, d88785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6433, d88785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6438 q = 1) (hb : d85724 q = 1) : d88806 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6438, d88806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10449 q ha hb
    | true =>
      simp only [d6438, d88806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10442 q ha hb
  have h9 (q : Pattern) (ha : d76983 q = 1) (hb : d85724 q = 1) : d88807 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76983, d88807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76983, d88807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6445 q = 1) (hb : d85724 q = 1) : d88756 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6445, d88756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10437 q ha hb
    | true =>
      simp only [d6445, d88756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d6446 q = 1) (hb : d85724 q = 1) : d88808 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6446, d88808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d6446, d88808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d76984 q = 1) (hb : d85724 q = 1) : d88809 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76984, d88809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76984, d88809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d76985 q = 1) (hb : d85724 q = 1) : d88810 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76985, d88810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d76985, d88810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d76986 q = 1) (hb : d85724 q = 1) : d88811 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76986, d88811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76986, d88811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d6452 q = 1) (hb : d85724 q = 1) : d88814 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6452, d88814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10453 q ha hb
    | true =>
      simp only [d6452, d88814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10451 q ha hb
  have h16 (q : Pattern) (ha : d6453 q = 1) (hb : d85724 q = 1) : d88815 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6453, d88815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6453, d88815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d6454 q = 1) (hb : d85724 q = 1) : d88816 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6454, d88816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d6454, d88816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d6455 q = 1) (hb : d85724 q = 1) : d88817 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6455, d88817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6455, d88817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d6457 q = 1) (hb : d85724 q = 1) : d88819 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6457, d88819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10454 q ha hb
    | true =>
      simp only [d6457, d88819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10452 q ha hb
  have h20 (q : Pattern) (ha : d6458 q = 1) (hb : d85724 q = 1) : d88820 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6458, d88820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6458, d88820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d6459 q = 1) (hb : d85724 q = 1) : d88821 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6459, d88821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d6459, d88821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d6462 q = 1) (hb : d85724 q = 1) : d88824 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6462, d88824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10455 q ha hb
    | true =>
      simp only [d6462, d88824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10456 q ha hb
  have h23 (q : Pattern) (ha : d76988 q = 1) (hb : d85724 q = 1) : d88825 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76988, d88825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d76988, d88825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d6466 q = 1) (hb : d85724 q = 1) : d88765 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6466, d88765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10439 q ha hb
    | true =>
      simp only [d6466, d88765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d6467 q = 1) (hb : d85724 q = 1) : d88826 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6467, d88826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d6467, d88826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d76989 q = 1) (hb : d85724 q = 1) : d88827 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76989, d88827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d76989, d88827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d76990 q = 1) (hb : d85724 q = 1) : d88828 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76990, d88828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d76990, d88828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d76991 q = 1) (hb : d85724 q = 1) : d88829 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76991, d88829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d76991, d88829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d76992 q = 1) (hb : d85724 q = 1) : d88830 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76992, d88830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d76992, d88830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro10458 (p : Pattern) (ha : d76999 p = 1) (hb : d85724 p = 1) : d88844 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6462 q = 1) (hb : d85724 q = 1) : d88824 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6462, d88824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10455 q ha hb
    | true =>
      simp only [d6462, d88824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10456 q ha hb
  have h2 (q : Pattern) (ha : d76988 q = 1) (hb : d85724 q = 1) : d88825 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76988, d88825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76988, d88825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6466 q = 1) (hb : d85724 q = 1) : d88765 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6466, d88765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10439 q ha hb
    | true =>
      simp only [d6466, d88765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6467 q = 1) (hb : d85724 q = 1) : d88826 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6467, d88826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6467, d88826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d76989 q = 1) (hb : d85724 q = 1) : d88827 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76989, d88827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76989, d88827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76997 q = 1) (hb : d85724 q = 1) : d88842 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76997, d88842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76997, d88842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76998 q = 1) (hb : d85724 q = 1) : d88843 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76998, d88843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76998, d88843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76999 q = 1) (hb : d85724 q = 1) : d88844 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76999, d88844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76999, d88844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10459 (p : Pattern) (ha : d1894 p = 1) (hb : d85723 p = 1) : d88851 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1882 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d1873 q = 1) : d1873 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1878 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1879 q = 1) (hb : d85721 q = 1) : d11808 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1879, d85721, d11808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d1879, d85721, d11808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1880 q = 1) (hb : d85721 q = 1) : d11809 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1880, d11809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1880, d11809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1881 q = 1) (hb : d85721 q = 1) : d11810 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1881, d11810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1881, d11810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d1878 q = 1) : d1878 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1888 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1889 q = 1) (hb : d85721 q = 1) : d11812 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1889, d85721, d11812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d1889, d85721, d11812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d1890 q = 1) (hb : d85721 q = 1) : d11813 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1890, d11813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1890, d11813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1891 q = 1) (hb : d85721 q = 1) : d11814 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1891, d11814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1891, d11814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1892 q = 1) (hb : d85721 q = 1) : d11815 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1892, d11815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1892, d11815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1893 q = 1) (hb : d85723 q = 1) : d88850 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1893, d85723, d88850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1893, d85723, d88850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d1894 q = 1) (hb : d85723 q = 1) : d88851 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1894, d88851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1894, d88851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro10460 (p : Pattern) (ha : d6494 p = 1) (hb : d85724 p = 1) : d88857 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1895 q = 1) (hb : d85723 q = 1) : d88852 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1895, d88852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10459 q ha hb
    | true =>
      simp only [d1895, d88852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1896 q = 1) (hb : d85723 q = 1) : d88853 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1896, d88853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1896, d88853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6491 q = 1) (hb : d85724 q = 1) : d88854 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6491, d85724, d88854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6491, d85724, d88854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6492 q = 1) (hb : d85724 q = 1) : d88855 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6492, d88855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6492, d88855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6493 q = 1) (hb : d85724 q = 1) : d88856 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6493, d88856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6493, d88856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6494 q = 1) (hb : d85724 q = 1) : d88857 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6494, d88857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6494, d88857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro10461 (p : Pattern) (ha : d6507 p = 1) (hb : d85723 p = 1) : d88863 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1892 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d6495 q = 1) : d6495 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6501 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6502 q = 1) (hb : d85721 q = 1) : d88858 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6502, d85721, d88858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d6502, d85721, d88858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d6503 q = 1) (hb : d85721 q = 1) : d88859 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6503, d88859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6503, d88859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6504 q = 1) (hb : d85721 q = 1) : d88860 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6504, d88860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6504, d88860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6505 q = 1) (hb : d85721 q = 1) : d88861 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6505, d88861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6505, d88861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d6506 q = 1) (hb : d85723 q = 1) : d88862 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6506, d85723, d88862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6506, d85723, d88862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d6507 q = 1) (hb : d85723 q = 1) : d88863 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6507, d88863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6507, d88863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro10462 (p : Pattern) (ha : d6513 p = 1) (hb : d85724 p = 1) : d88869 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6508 q = 1) (hb : d85723 q = 1) : d88864 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6508, d88864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10461 q ha hb
    | true =>
      simp only [d6508, d88864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6509 q = 1) (hb : d85723 q = 1) : d88865 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6509, d88865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6509, d88865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6510 q = 1) (hb : d85724 q = 1) : d88866 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6510, d85724, d88866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6510, d85724, d88866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6511 q = 1) (hb : d85724 q = 1) : d88867 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6511, d88867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6511, d88867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6512 q = 1) (hb : d85724 q = 1) : d88868 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6512, d88868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6512, d88868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6513 q = 1) (hb : d85724 q = 1) : d88869 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6513, d88869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6513, d88869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro10463 (p : Pattern) (ha : d1899 p = 1) (hb : d85723 p = 1) : d88873 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1892 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d1878 q = 1) : d1878 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1888 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1889 q = 1) (hb : d85721 q = 1) : d11812 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1889, d85721, d11812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d1889, d85721, d11812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1890 q = 1) (hb : d85721 q = 1) : d11813 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1890, d11813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1890, d11813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1891 q = 1) (hb : d85721 q = 1) : d11814 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1891, d11814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1891, d11814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1897 q = 1) (hb : d85721 q = 1) : d11820 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1897, d11820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1897, d11820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d1898 q = 1) (hb : d85723 q = 1) : d88872 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1898, d85723, d88872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1898, d85723, d88872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d1899 q = 1) (hb : d85723 q = 1) : d88873 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1899, d88873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1899, d88873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro10464 (p : Pattern) (ha : d6524 p = 1) (hb : d85724 p = 1) : d88879 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1900 q = 1) (hb : d85723 q = 1) : d88874 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1900, d88874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10463 q ha hb
    | true =>
      simp only [d1900, d88874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1901 q = 1) (hb : d85723 q = 1) : d88875 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1901, d88875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1901, d88875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6521 q = 1) (hb : d85724 q = 1) : d88876 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6521, d85724, d88876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6521, d85724, d88876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6522 q = 1) (hb : d85724 q = 1) : d88877 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6522, d88877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6522, d88877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6523 q = 1) (hb : d85724 q = 1) : d88878 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6523, d88878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6523, d88878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6524 q = 1) (hb : d85724 q = 1) : d88879 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6524, d88879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6524, d88879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro10465 (p : Pattern) (ha : d77009 p = 1) (hb : d85724 p = 1) : d88885 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6514 q = 1) (hb : d85724 q = 1) : d88870 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6514, d88870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10460 q ha hb
    | true =>
      simp only [d6514, d88870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10462 q ha hb
  have h2 (q : Pattern) (ha : d77005 q = 1) (hb : d85724 q = 1) : d88871 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77005, d88871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77005, d88871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6525 q = 1) (hb : d85724 q = 1) : d88880 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6525, d88880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10464 q ha hb
    | true =>
      simp only [d6525, d88880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6526 q = 1) (hb : d85724 q = 1) : d88881 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6526, d88881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6526, d88881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77006 q = 1) (hb : d85724 q = 1) : d88882 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77006, d88882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77006, d88882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77007 q = 1) (hb : d85724 q = 1) : d88883 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77007, d88883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77007, d88883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77008 q = 1) (hb : d85724 q = 1) : d88884 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77008, d88884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77008, d88884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77009 q = 1) (hb : d85724 q = 1) : d88885 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77009, d88885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77009, d88885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10466 (p : Pattern) (ha : d77015 p = 1) (hb : d85724 p = 1) : d88891 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6410 q = 1) (hb : d85724 q = 1) : d88762 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6410, d88762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6410, d88762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10438 q ha hb
  have h2 (q : Pattern) (ha : d6411 q = 1) (hb : d85724 q = 1) : d88763 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6411, d88763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6411, d88763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6419 q = 1) (hb : d85724 q = 1) : d88771 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6419, d88771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10438 q ha hb
    | true =>
      simp only [d6419, d88771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10440 q ha hb
  have h4 (q : Pattern) (ha : d6420 q = 1) (hb : d85724 q = 1) : d88772 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6420, d88772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6420, d88772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6421 q = 1) (hb : d85724 q = 1) : d88773 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d6421, d88773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6421, d88773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76993 q = 1) (hb : d85724 q = 1) : d88831 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76993, d88831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10450 q ha hb
    | true =>
      simp only [d76993, d88831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10457 q ha hb
  have h7 (q : Pattern) (ha : d6479 q = 1) (hb : d85724 q = 1) : d88838 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6479, d88838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10443 q ha hb
    | true =>
      simp only [d6479, d88838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10431 q ha hb
  have h8 (q : Pattern) (ha : d76994 q = 1) (hb : d85724 q = 1) : d88839 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76994, d88839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76994, d88839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76995 q = 1) (hb : d85724 q = 1) : d88840 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76995, d88840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76995, d88840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d76996 q = 1) (hb : d85724 q = 1) : d88841 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76996, d88841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76996, d88841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d77000 q = 1) (hb : d85724 q = 1) : d88845 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77000, d88845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77000, d88845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10458 q ha hb
  have h12 (q : Pattern) (ha : d1848 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10432 q ha hb
  have h13 (q : Pattern) (ha : d77001 q = 1) (hb : d85724 q = 1) : d88846 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77001, d88846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d77001, d88846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d77002 q = 1) (hb : d85724 q = 1) : d88847 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77002, d88847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d77002, d88847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d77003 q = 1) (hb : d85724 q = 1) : d88848 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77003, d88848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d77003, d88848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d77004 q = 1) (hb : d85724 q = 1) : d88849 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77004, d88849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d77004, d88849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d77010 q = 1) (hb : d85724 q = 1) : d88886 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77010, d88886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77010, d88886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10465 q ha hb
  have h18 (q : Pattern) (ha : d1981 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10435 q ha hb
  have h19 (q : Pattern) (ha : d77011 q = 1) (hb : d85724 q = 1) : d88887 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77011, d88887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d77011, d88887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d77012 q = 1) (hb : d85724 q = 1) : d88888 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77012, d88888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d77012, d88888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d77013 q = 1) (hb : d85724 q = 1) : d88889 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77013, d88889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d77013, d88889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d77014 q = 1) (hb : d85724 q = 1) : d88890 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77014, d88890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d77014, d88890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d77015 q = 1) (hb : d85724 q = 1) : d88891 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d77015, d88891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d77015, d88891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro10467 (p : Pattern) (ha : d77021 p = 1) (hb : d85724 p = 1) : d88897 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77016 q = 1) (hb : d85724 q = 1) : d88892 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d77016, d88892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77016, d88892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10466 q ha hb
  have h2 (q : Pattern) (ha : d77017 q = 1) (hb : d85724 q = 1) : d88893 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d77017, d88893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77017, d88893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d77018 q = 1) (hb : d85724 q = 1) : d88894 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d77018, d88894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77018, d88894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77019 q = 1) (hb : d85724 q = 1) : d88895 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d77019, d88895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77019, d88895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d77020 q = 1) (hb : d85724 q = 1) : d88896 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d77020, d88896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77020, d88896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77021 q = 1) (hb : d85724 q = 1) : d88897 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d77021, d88897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77021, d88897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10468 (p : Pattern) (ha : d2096 p = 1) (hb : d85723 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2090 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2095 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d2095, d85723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2095, d85723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2096 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d2096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro10469 (p : Pattern) (ha : d2106 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2097 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10468 q ha hb
    | true =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2098 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2103 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2103, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2104 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2105 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2106 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10470 (p : Pattern) (ha : d2116 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2097 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10468 q ha hb
    | true =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2103 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2103, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2104 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2105 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d2116 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro10471 (p : Pattern) (ha : d2316 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2305 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10469 q ha hb
    | true =>
      simp only [d2305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2306 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2307 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2308 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2309 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2311 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10470 q ha hb
    | true =>
      simp only [d2311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2312 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2313 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2314 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2315 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2316 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro10472 (p : Pattern) (ha : d2325 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2311 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10470 q ha hb
    | true =>
      simp only [d2311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2312 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2313 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2314 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2315 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2325 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10473 (p : Pattern) (ha : d2385 p = 1) (hb : d85723 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2375 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2384 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d2384, d85723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2384, d85723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2385 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d2385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro10474 (p : Pattern) (ha : d2452 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2386 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10473 q ha hb
    | true =>
      simp only [d2386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2387 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2449 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2449, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2449, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2450 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2451 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d2452 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro10475 (p : Pattern) (ha : d2458 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2453 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10474 q ha hb
    | true =>
      simp only [d2453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2454 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2455 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2456 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2457 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2458 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10476 (p : Pattern) (ha : d2092 p = 1) (hb : d85723 p = 1) : d88903 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2089 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d2072 q = 1) : d2072 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2085 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2086 q = 1) (hb : d85721 q = 1) : d11912 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2086, d85721, d11912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d2086, d85721, d11912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d2087 q = 1) (hb : d85721 q = 1) : d11913 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2087, d11913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2087, d11913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2088 q = 1) (hb : d85721 q = 1) : d11914 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2088, d11914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2088, d11914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2090 q = 1) (hb : d85721 q = 1) : d11916 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2090, d11916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2090, d11916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d2091 q = 1) (hb : d85723 q = 1) : d88902 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d2091, d85723, d88902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2091, d85723, d88902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d2092 q = 1) (hb : d85723 q = 1) : d88903 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d2092, d88903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2092, d88903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro10477 (p : Pattern) (ha : d6550 p = 1) (hb : d85724 p = 1) : d88909 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2093 q = 1) (hb : d85723 q = 1) : d88904 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d88904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10476 q ha hb
    | true =>
      simp only [d2093, d88904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2094 q = 1) (hb : d85723 q = 1) : d88905 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d88905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2094, d88905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6547 q = 1) (hb : d85724 q = 1) : d88906 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6547, d85724, d88906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6547, d85724, d88906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6548 q = 1) (hb : d85724 q = 1) : d88907 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6548, d88907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6548, d88907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6549 q = 1) (hb : d85724 q = 1) : d88908 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6549, d88908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6549, d88908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6550 q = 1) (hb : d85724 q = 1) : d88909 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6550, d88909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6550, d88909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10478 (p : Pattern) (ha : d6556 p = 1) (hb : d85724 p = 1) : d88915 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6551 q = 1) (hb : d85724 q = 1) : d88910 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6551, d88910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10477 q ha hb
    | true =>
      simp only [d6551, d88910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10469 q ha hb
  have h2 (q : Pattern) (ha : d6552 q = 1) (hb : d85724 q = 1) : d88911 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6552, d88911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6552, d88911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6553 q = 1) (hb : d85724 q = 1) : d88912 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6553, d88912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6553, d88912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6554 q = 1) (hb : d85724 q = 1) : d88913 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6554, d88913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6554, d88913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6555 q = 1) (hb : d85724 q = 1) : d88914 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6555, d88914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6555, d88914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6556 q = 1) (hb : d85724 q = 1) : d88915 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6556, d88915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6556, d88915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro10479 (p : Pattern) (ha : d6559 p = 1) (hb : d85724 p = 1) : d88918 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2093 q = 1) (hb : d85723 q = 1) : d88904 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d88904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10476 q ha hb
    | true =>
      simp only [d2093, d88904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2094 q = 1) (hb : d85723 q = 1) : d88905 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d88905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2094, d88905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6547 q = 1) (hb : d85724 q = 1) : d88906 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6547, d85724, d88906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6547, d85724, d88906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6548 q = 1) (hb : d85724 q = 1) : d88907 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6548, d88907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6548, d88907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6549 q = 1) (hb : d85724 q = 1) : d88908 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6549, d88908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6549, d88908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6559 q = 1) (hb : d85724 q = 1) : d88918 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6559, d88918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6559, d88918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro10480 (p : Pattern) (ha : d6565 p = 1) (hb : d85724 p = 1) : d88924 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6551 q = 1) (hb : d85724 q = 1) : d88910 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6551, d88910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10477 q ha hb
    | true =>
      simp only [d6551, d88910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10469 q ha hb
  have h2 (q : Pattern) (ha : d6552 q = 1) (hb : d85724 q = 1) : d88911 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6552, d88911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6552, d88911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6553 q = 1) (hb : d85724 q = 1) : d88912 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6553, d88912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6553, d88912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6554 q = 1) (hb : d85724 q = 1) : d88913 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6554, d88913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6554, d88913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6555 q = 1) (hb : d85724 q = 1) : d88914 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6555, d88914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6555, d88914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6560 q = 1) (hb : d85724 q = 1) : d88919 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6560, d88919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10479 q ha hb
    | true =>
      simp only [d6560, d88919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10470 q ha hb
  have h7 (q : Pattern) (ha : d6561 q = 1) (hb : d85724 q = 1) : d88920 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6561, d88920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6561, d88920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6562 q = 1) (hb : d85724 q = 1) : d88921 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6562, d88921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6562, d88921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d6563 q = 1) (hb : d85724 q = 1) : d88922 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6563, d88922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6563, d88922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6564 q = 1) (hb : d85724 q = 1) : d88923 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6564, d88923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6564, d88923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6565 q = 1) (hb : d85724 q = 1) : d88924 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6565, d88924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6565, d88924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro10481 (p : Pattern) (ha : d5258 p = 1) (hb : d85723 p = 1) : d88953 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2089 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d5237 q = 1) : d5237 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d5252 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5253 q = 1) (hb : d85721 q = 1) : d88948 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5253, d85721, d88948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d5253, d85721, d88948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d5254 q = 1) (hb : d85721 q = 1) : d88949 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5254, d88949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5254, d88949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5255 q = 1) (hb : d85721 q = 1) : d88950 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5255, d88950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5255, d88950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5256 q = 1) (hb : d85721 q = 1) : d88951 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5256, d88951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5256, d88951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d5257 q = 1) (hb : d85723 q = 1) : d88952 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d5257, d85723, d88952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5257, d85723, d88952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d5258 q = 1) (hb : d85723 q = 1) : d88953 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d5258, d88953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5258, d88953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro10482 (p : Pattern) (ha : d5264 p = 1) (hb : d85724 p = 1) : d88959 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5259 q = 1) (hb : d85723 q = 1) : d88954 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5259, d88954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10481 q ha hb
    | true =>
      simp only [d5259, d88954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5260 q = 1) (hb : d85723 q = 1) : d88955 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5260, d88955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5260, d88955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5261 q = 1) (hb : d85724 q = 1) : d88956 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5261, d85724, d88956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5261, d85724, d88956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5262 q = 1) (hb : d85724 q = 1) : d88957 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5262, d88957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5262, d88957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d5263 q = 1) (hb : d85724 q = 1) : d88958 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5263, d88958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5263, d88958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d5264 q = 1) (hb : d85724 q = 1) : d88959 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5264, d88959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5264, d88959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10483 (p : Pattern) (ha : d6625 p = 1) (hb : d85724 p = 1) : d88991 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6620 q = 1) (hb : d85724 q = 1) : d88986 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6620, d88986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10482 q ha hb
    | true =>
      simp only [d6620, d88986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10469 q ha hb
  have h2 (q : Pattern) (ha : d6621 q = 1) (hb : d85724 q = 1) : d88987 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6621, d88987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6621, d88987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6622 q = 1) (hb : d85724 q = 1) : d88988 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6622, d88988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6622, d88988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6623 q = 1) (hb : d85724 q = 1) : d88989 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6623, d88989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6623, d88989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6624 q = 1) (hb : d85724 q = 1) : d88990 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6624, d88990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6624, d88990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2305 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10469 q ha hb
    | true =>
      simp only [d2305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2306 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2307 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2308 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2309 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6625 q = 1) (hb : d85724 q = 1) : d88991 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6625, d88991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6625, d88991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro10484 (p : Pattern) (ha : d2129 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2097 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10468 q ha hb
    | true =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2098 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2103 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2103, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2104 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2128 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2129 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10485 (p : Pattern) (ha : d2139 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2097 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10468 q ha hb
    | true =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2098 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2103 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2103, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2137 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2138 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2139 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10486 (p : Pattern) (ha : d6570 p = 1) (hb : d85724 p = 1) : d88929 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2093 q = 1) (hb : d85723 q = 1) : d88904 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d88904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10476 q ha hb
    | true =>
      simp only [d2093, d88904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2094 q = 1) (hb : d85723 q = 1) : d88905 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d88905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2094, d88905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6547 q = 1) (hb : d85724 q = 1) : d88906 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6547, d85724, d88906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6547, d85724, d88906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6548 q = 1) (hb : d85724 q = 1) : d88907 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6548, d88907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6548, d88907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6569 q = 1) (hb : d85724 q = 1) : d88928 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6569, d88928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6569, d88928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6570 q = 1) (hb : d85724 q = 1) : d88929 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6570, d88929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6570, d88929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10487 (p : Pattern) (ha : d6577 p = 1) (hb : d85724 p = 1) : d88936 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2093 q = 1) (hb : d85723 q = 1) : d88904 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d88904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10476 q ha hb
    | true =>
      simp only [d2093, d88904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2094 q = 1) (hb : d85723 q = 1) : d88905 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d88905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2094, d88905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6547 q = 1) (hb : d85724 q = 1) : d88906 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6547, d85724, d88906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6547, d85724, d88906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6575 q = 1) (hb : d85724 q = 1) : d88934 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6575, d88934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6575, d88934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6576 q = 1) (hb : d85724 q = 1) : d88935 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6576, d88935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6576, d88935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6577 q = 1) (hb : d85724 q = 1) : d88936 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6577, d88936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6577, d88936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10488 (p : Pattern) (ha : d2155 p = 1) (hb : d85723 p = 1) : d88941 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2153 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d2070 q = 1) : d2070 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2072 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2073 q = 1) (hb : d85721 q = 1) : d11909 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2073, d85721, d11909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d2073, d85721, d11909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d2074 q = 1) (hb : d85721 q = 1) : d11910 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2074, d11910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2074, d11910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2075 q = 1) (hb : d85721 q = 1) : d11911 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2075, d11911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2075, d11911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d2072 q = 1) : d2072 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d2085 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d2086 q = 1) (hb : d85721 q = 1) : d11912 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2086, d85721, d11912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d2086, d85721, d11912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d2087 q = 1) (hb : d85721 q = 1) : d11913 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2087, d11913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2087, d11913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2088 q = 1) (hb : d85721 q = 1) : d11914 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2088, d11914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2088, d11914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d2089 q = 1) (hb : d85721 q = 1) : d11915 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2089, d11915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2089, d11915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d2154 q = 1) (hb : d85723 q = 1) : d88940 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d2154, d85723, d88940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2154, d85723, d88940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d2155 q = 1) (hb : d85723 q = 1) : d88941 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d2155, d88941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d2155, d88941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro10489 (p : Pattern) (ha : d6584 p = 1) (hb : d85724 p = 1) : d88947 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2156 q = 1) (hb : d85723 q = 1) : d88942 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2156, d88942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10488 q ha hb
    | true =>
      simp only [d2156, d88942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2157 q = 1) (hb : d85723 q = 1) : d88943 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2157, d88943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2157, d88943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6581 q = 1) (hb : d85724 q = 1) : d88944 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6581, d85724, d88944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6581, d85724, d88944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6582 q = 1) (hb : d85724 q = 1) : d88945 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6582, d88945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6582, d88945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6583 q = 1) (hb : d85724 q = 1) : d88946 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6583, d88946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6583, d88946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6584 q = 1) (hb : d85724 q = 1) : d88947 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6584, d88947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6584, d88947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10490 (p : Pattern) (ha : d77030 p = 1) (hb : d85724 p = 1) : d88966 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6571 q = 1) (hb : d85724 q = 1) : d88930 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6571, d88930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10486 q ha hb
    | true =>
      simp only [d6571, d88930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10484 q ha hb
  have h2 (q : Pattern) (ha : d6572 q = 1) (hb : d85724 q = 1) : d88931 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6572, d88931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6572, d88931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6573 q = 1) (hb : d85724 q = 1) : d88932 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6573, d88932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6573, d88932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6574 q = 1) (hb : d85724 q = 1) : d88933 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6574, d88933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6574, d88933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6578 q = 1) (hb : d85724 q = 1) : d88937 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6578, d88937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10487 q ha hb
    | true =>
      simp only [d6578, d88937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10485 q ha hb
  have h6 (q : Pattern) (ha : d6579 q = 1) (hb : d85724 q = 1) : d88938 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6579, d88938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6579, d88938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6580 q = 1) (hb : d85724 q = 1) : d88939 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6580, d88939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6580, d88939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6585 q = 1) (hb : d85724 q = 1) : d88960 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6585, d88960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10489 q ha hb
    | true =>
      simp only [d6585, d88960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10482 q ha hb
  have h9 (q : Pattern) (ha : d77026 q = 1) (hb : d85724 q = 1) : d88961 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77026, d88961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d77026, d88961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6592 q = 1) (hb : d85724 q = 1) : d88910 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6592, d88910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10477 q ha hb
    | true =>
      simp only [d6592, d88910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d6593 q = 1) (hb : d85724 q = 1) : d88962 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6593, d88962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d6593, d88962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d77027 q = 1) (hb : d85724 q = 1) : d88963 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77027, d88963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d77027, d88963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d77028 q = 1) (hb : d85724 q = 1) : d88964 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77028, d88964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d77028, d88964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d77029 q = 1) (hb : d85724 q = 1) : d88965 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77029, d88965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77029, d88965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d77030 q = 1) (hb : d85724 q = 1) : d88966 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77030, d88966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77030, d88966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro10491 (p : Pattern) (ha : d2282 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2097 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10468 q ha hb
    | true =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2098 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2103 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2103, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2104 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2128 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2282 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro10492 (p : Pattern) (ha : d2288 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2097 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10468 q ha hb
    | true =>
      simp only [d2097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2098 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2103 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2103, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2137 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2138 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2288 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro10493 (p : Pattern) (ha : d6598 p = 1) (hb : d85724 p = 1) : d88967 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2093 q = 1) (hb : d85723 q = 1) : d88904 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d88904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10476 q ha hb
    | true =>
      simp only [d2093, d88904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2094 q = 1) (hb : d85723 q = 1) : d88905 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d88905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2094, d88905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6547 q = 1) (hb : d85724 q = 1) : d88906 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6547, d85724, d88906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6547, d85724, d88906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6548 q = 1) (hb : d85724 q = 1) : d88907 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6548, d88907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6548, d88907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6569 q = 1) (hb : d85724 q = 1) : d88928 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6569, d88928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6569, d88928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6598 q = 1) (hb : d85724 q = 1) : d88967 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6598, d88967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6598, d88967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro10494 (p : Pattern) (ha : d6603 p = 1) (hb : d85724 p = 1) : d88972 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2093 q = 1) (hb : d85723 q = 1) : d88904 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d88904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10476 q ha hb
    | true =>
      simp only [d2093, d88904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2094 q = 1) (hb : d85723 q = 1) : d88905 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d88905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2094, d88905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6547 q = 1) (hb : d85724 q = 1) : d88906 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6547, d85724, d88906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6547, d85724, d88906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6575 q = 1) (hb : d85724 q = 1) : d88934 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6575, d88934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6575, d88934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6576 q = 1) (hb : d85724 q = 1) : d88935 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6576, d88935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6576, d88935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6603 q = 1) (hb : d85724 q = 1) : d88972 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6603, d88972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6603, d88972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro10495 (p : Pattern) (ha : d6607 p = 1) (hb : d85724 p = 1) : d88976 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2156 q = 1) (hb : d85723 q = 1) : d88942 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2156, d88942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10488 q ha hb
    | true =>
      simp only [d2156, d88942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2157 q = 1) (hb : d85723 q = 1) : d88943 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2157, d88943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2157, d88943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6581 q = 1) (hb : d85724 q = 1) : d88944 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6581, d85724, d88944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6581, d85724, d88944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6582 q = 1) (hb : d85724 q = 1) : d88945 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6582, d88945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6582, d88945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6583 q = 1) (hb : d85724 q = 1) : d88946 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6583, d88946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6583, d88946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6607 q = 1) (hb : d85724 q = 1) : d88976 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6607, d88976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6607, d88976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro10496 (p : Pattern) (ha : d6608 p = 1) (hb : d85724 p = 1) : d88977 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5259 q = 1) (hb : d85723 q = 1) : d88954 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5259, d88954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10481 q ha hb
    | true =>
      simp only [d5259, d88954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5260 q = 1) (hb : d85723 q = 1) : d88955 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5260, d88955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5260, d88955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5261 q = 1) (hb : d85724 q = 1) : d88956 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5261, d85724, d88956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5261, d85724, d88956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d5262 q = 1) (hb : d85724 q = 1) : d88957 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5262, d88957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5262, d88957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5263 q = 1) (hb : d85724 q = 1) : d88958 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5263, d88958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5263, d88958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6608 q = 1) (hb : d85724 q = 1) : d88977 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6608, d88977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6608, d88977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro10497 (p : Pattern) (ha : d77035 p = 1) (hb : d85724 p = 1) : d88984 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6571 q = 1) (hb : d85724 q = 1) : d88930 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6571, d88930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10486 q ha hb
    | true =>
      simp only [d6571, d88930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10484 q ha hb
  have h2 (q : Pattern) (ha : d6572 q = 1) (hb : d85724 q = 1) : d88931 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6572, d88931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6572, d88931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6573 q = 1) (hb : d85724 q = 1) : d88932 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6573, d88932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6573, d88932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6574 q = 1) (hb : d85724 q = 1) : d88933 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6574, d88933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6574, d88933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6578 q = 1) (hb : d85724 q = 1) : d88937 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6578, d88937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10487 q ha hb
    | true =>
      simp only [d6578, d88937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10485 q ha hb
  have h6 (q : Pattern) (ha : d6579 q = 1) (hb : d85724 q = 1) : d88938 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6579, d88938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6579, d88938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6580 q = 1) (hb : d85724 q = 1) : d88939 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6580, d88939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6580, d88939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6585 q = 1) (hb : d85724 q = 1) : d88960 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6585, d88960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10489 q ha hb
    | true =>
      simp only [d6585, d88960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10482 q ha hb
  have h9 (q : Pattern) (ha : d77026 q = 1) (hb : d85724 q = 1) : d88961 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77026, d88961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d77026, d88961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6592 q = 1) (hb : d85724 q = 1) : d88910 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6592, d88910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10477 q ha hb
    | true =>
      simp only [d6592, d88910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d6593 q = 1) (hb : d85724 q = 1) : d88962 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6593, d88962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d6593, d88962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d77027 q = 1) (hb : d85724 q = 1) : d88963 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77027, d88963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d77027, d88963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d77028 q = 1) (hb : d85724 q = 1) : d88964 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77028, d88964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d77028, d88964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d77029 q = 1) (hb : d85724 q = 1) : d88965 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77029, d88965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77029, d88965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d6599 q = 1) (hb : d85724 q = 1) : d88968 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6599, d88968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10493 q ha hb
    | true =>
      simp only [d6599, d88968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10491 q ha hb
  have h16 (q : Pattern) (ha : d6600 q = 1) (hb : d85724 q = 1) : d88969 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6600, d88969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6600, d88969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d6601 q = 1) (hb : d85724 q = 1) : d88970 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6601, d88970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d6601, d88970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d6602 q = 1) (hb : d85724 q = 1) : d88971 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6602, d88971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6602, d88971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d6604 q = 1) (hb : d85724 q = 1) : d88973 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6604, d88973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10494 q ha hb
    | true =>
      simp only [d6604, d88973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10492 q ha hb
  have h20 (q : Pattern) (ha : d6605 q = 1) (hb : d85724 q = 1) : d88974 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6605, d88974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6605, d88974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d6606 q = 1) (hb : d85724 q = 1) : d88975 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6606, d88975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d6606, d88975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d6609 q = 1) (hb : d85724 q = 1) : d88978 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6609, d88978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10495 q ha hb
    | true =>
      simp only [d6609, d88978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10496 q ha hb
  have h23 (q : Pattern) (ha : d77031 q = 1) (hb : d85724 q = 1) : d88979 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77031, d88979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d77031, d88979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d6613 q = 1) (hb : d85724 q = 1) : d88919 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6613, d88919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10479 q ha hb
    | true =>
      simp only [d6613, d88919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d6614 q = 1) (hb : d85724 q = 1) : d88980 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6614, d88980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d6614, d88980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d77032 q = 1) (hb : d85724 q = 1) : d88981 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77032, d88981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d77032, d88981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d77033 q = 1) (hb : d85724 q = 1) : d88982 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77033, d88982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d77033, d88982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d77034 q = 1) (hb : d85724 q = 1) : d88983 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77034, d88983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d77034, d88983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d77035 q = 1) (hb : d85724 q = 1) : d88984 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77035, d88984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d77035, d88984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro10498 (p : Pattern) (ha : d77042 p = 1) (hb : d85724 p = 1) : d88998 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6609 q = 1) (hb : d85724 q = 1) : d88978 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6609, d88978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10495 q ha hb
    | true =>
      simp only [d6609, d88978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10496 q ha hb
  have h2 (q : Pattern) (ha : d77031 q = 1) (hb : d85724 q = 1) : d88979 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77031, d88979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77031, d88979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6613 q = 1) (hb : d85724 q = 1) : d88919 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6613, d88919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10479 q ha hb
    | true =>
      simp only [d6613, d88919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6614 q = 1) (hb : d85724 q = 1) : d88980 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6614, d88980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6614, d88980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77032 q = 1) (hb : d85724 q = 1) : d88981 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77032, d88981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77032, d88981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77040 q = 1) (hb : d85724 q = 1) : d88996 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77040, d88996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77040, d88996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77041 q = 1) (hb : d85724 q = 1) : d88997 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77041, d88997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77041, d88997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77042 q = 1) (hb : d85724 q = 1) : d88998 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77042, d88998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77042, d88998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro10499 (p : Pattern) (ha : d2372 p = 1) (hb : d85723 p = 1) : d89005 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2360 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d2351 q = 1) : d2351 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2356 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2357 q = 1) (hb : d85721 q = 1) : d12080 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2357, d85721, d12080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d2357, d85721, d12080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d2358 q = 1) (hb : d85721 q = 1) : d12081 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2358, d12081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2358, d12081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2359 q = 1) (hb : d85721 q = 1) : d12082 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2359, d12082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2359, d12082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d2356 q = 1) : d2356 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d2366 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d2367 q = 1) (hb : d85721 q = 1) : d12084 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2367, d85721, d12084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d2367, d85721, d12084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d2368 q = 1) (hb : d85721 q = 1) : d12085 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2368, d12085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2368, d12085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2369 q = 1) (hb : d85721 q = 1) : d12086 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2369, d12086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2369, d12086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d2370 q = 1) (hb : d85721 q = 1) : d12087 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2370, d12087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2370, d12087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d2371 q = 1) (hb : d85723 q = 1) : d89004 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d2371, d85723, d89004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2371, d85723, d89004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d2372 q = 1) (hb : d85723 q = 1) : d89005 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d2372, d89005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d2372, d89005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
end NetHack.Soko22Hazard87
