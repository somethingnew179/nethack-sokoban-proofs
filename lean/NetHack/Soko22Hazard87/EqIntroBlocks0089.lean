import NetHack.Soko22Hazard87.EqIntroBlocks0088
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro22250 (p : Pattern) (selected : d223422 p = 1) : d225465 p = 1 := by
  have h0 (q : Pattern) (selected : d223309 q = 1) : d223309 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223318 q = 1) : d223318 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d223347 q = 1) : d223347 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d223386 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22245 q selected
    | true =>
      simp only [d223386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22246 q selected
  have h4 (q : Pattern) (selected : d223387 q = 1) : d225456 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223387, d225456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223387, d225456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223393 q = 1) : d223393 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d223394 q = 1) : d225457 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223394, d225457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223394, d225457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223395 q = 1) : d225458 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223395, d225458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223395, d225458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223396 q = 1) : d225459 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d223396, d225459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223396, d225459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d223403 q = 1) : d223403 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d223408 q = 1) : d223408 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d223411 q = 1) : d223411 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d223414 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22248 q selected
    | true =>
      simp only [d223414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22249 q selected
  have h13 (q : Pattern) (selected : d223415 q = 1) : d225461 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223415, d225461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d223415, d225461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d223418 q = 1) : d223418 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d223419 q = 1) : d225462 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223419, d225462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d223419, d225462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d223420 q = 1) : d225463 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223420, d225463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d223420, d225463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d223421 q = 1) : d225464 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d223421, d225464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d223421, d225464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d223422 q = 1) : d225465 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d223422, d225465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d223422, d225465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro22251 (p : Pattern) (selected : d223447 p = 1) : d225472 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223411 q = 1) : d223411 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d223414 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22248 q selected
    | true =>
      simp only [d223414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22249 q selected
  have h3 (q : Pattern) (selected : d223415 q = 1) : d225461 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223415, d225461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223415, d225461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223418 q = 1) : d223418 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d223419 q = 1) : d225462 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223419, d225462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223419, d225462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223445 q = 1) : d225470 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223445, d225470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223445, d225470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223446 q = 1) : d225471 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d223446, d225471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223446, d225471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223447 q = 1) : d225472 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d223447, d225472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223447, d225472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22252 (p : Pattern) (selected : d223512 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d118097 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9282 q selected
  have h2 (q : Pattern) (selected : d117911 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9282 q selected
    | true =>
      simp only [d117911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117912 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118099 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118100 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223506 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d223506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22238 q selected
  have h8 (q : Pattern) (selected : d223348 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d223348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22238 q selected
    | true =>
      simp only [d223348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d223507 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d223507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d223349 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d223349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d223349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d223508 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d223508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d223508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d223509 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d223509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d223509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d223510 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d118114 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9287 q selected
  have h15 (q : Pattern) (selected : d117928 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9287 q selected
    | true =>
      simp only [d117928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d118115 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d118115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d117929 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d117929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d118116 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d118116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d118117 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d118117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d223511 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d223511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d223512 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d223512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro22253 (p : Pattern) (selected : d223514 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d118101 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9283 q selected
  have h2 (q : Pattern) (selected : d117915 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9283 q selected
    | true =>
      simp only [d117915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118102 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117916 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118103 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118104 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118114 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9287 q selected
  have h8 (q : Pattern) (selected : d117928 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9287 q selected
    | true =>
      simp only [d117928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d118115 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117929 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d118116 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d118116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d118117 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d118117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d223513 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d118118 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d118118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d223514 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d223514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22254 (p : Pattern) (selected : d223518 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d118114 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9287 q selected
  have h2 (q : Pattern) (selected : d117928 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9287 q selected
    | true =>
      simp only [d117928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118115 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117929 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118116 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118117 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118118 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223518 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22255 (p : Pattern) (selected : d223523 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d118106 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9285 q selected
  have h2 (q : Pattern) (selected : d117920 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9285 q selected
    | true =>
      simp only [d117920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118107 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117921 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118108 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118109 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118123 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223523 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22256 (p : Pattern) (selected : d223529 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223515 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22252 q selected
    | true =>
      simp only [d223515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22253 q selected
  have h2 (q : Pattern) (selected : d223516 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223517 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223519 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22253 q selected
    | true =>
      simp only [d223519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22254 q selected
  have h5 (q : Pattern) (selected : d223520 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223521 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223522 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223524 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22253 q selected
    | true =>
      simp only [d223524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22255 q selected
  have h9 (q : Pattern) (selected : d223525 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d223526 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d223527 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d223527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d223528 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d223528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d223529 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d223529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d223529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro22257 (p : Pattern) (selected : d223533 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223524 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22253 q selected
    | true =>
      simp only [d223524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22255 q selected
  have h2 (q : Pattern) (selected : d223525 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223526 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223527 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223532 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d223532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223533 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d223533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22258 (p : Pattern) (selected : d223539 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223530 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22256 q selected
    | true =>
      simp only [d223530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223531 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223534 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22257 q selected
    | true =>
      simp only [d223534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223535 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223536 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223537 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223538 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223539 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22259 (p : Pattern) (selected : d223543 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223534 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22257 q selected
    | true =>
      simp only [d223534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223535 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223540 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223541 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223542 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223543 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22260 (p : Pattern) (selected : d223559 p = 1) : d225482 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223505 q = 1) : d223505 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d223544 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22258 q selected
    | true =>
      simp only [d223544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22259 q selected
  have h3 (q : Pattern) (selected : d223545 q = 1) : d225478 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223545, d225478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223545, d225478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223555 q = 1) : d223555 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d223556 q = 1) : d225479 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223556, d225479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223556, d225479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223557 q = 1) : d225480 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223557, d225480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223557, d225480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223558 q = 1) : d225481 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d223558, d225481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223558, d225481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223559 q = 1) : d225482 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d223559, d225482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223559, d225482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22261 (p : Pattern) (selected : d223576 p = 1) : d225488 p = 1 := by
  have h0 (q : Pattern) (selected : d223301 q = 1) : d223301 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223423 q = 1) : d225466 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d223423, d225466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22247 q selected
    | true =>
      simp only [d223423, d225466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22250 q selected
  have h2 (q : Pattern) (selected : d223441 q = 1) : d223441 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d223442 q = 1) : d225467 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d223442, d225467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223442, d225467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d223443 q = 1) : d225468 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d223443, d225468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223443, d225468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223444 q = 1) : d225469 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d223444, d225469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223444, d225469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223448 q = 1) : d225473 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d223448, d225473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223448, d225473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22251 q selected
  have h8 (q : Pattern) (selected : d223450 q = 1) : d223450 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d223451 q = 1) : d225474 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d223451, d225474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223451, d225474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d223452 q = 1) : d225475 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d223452, d225475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d223452, d225475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d223453 q = 1) : d225476 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d223453, d225476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d223453, d225476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d223454 q = 1) : d225477 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d223454, d225477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223454, d225477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d223560 q = 1) : d225483 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d223560, d225483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223560, d225483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22260 q selected
  have h14 (q : Pattern) (selected : d223571 q = 1) : d223571 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d223572 q = 1) : d225484 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d223572, d225484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d223572, d225484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d223573 q = 1) : d225485 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d223573, d225485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d223573, d225485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d223574 q = 1) : d225486 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d223574, d225486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d223574, d225486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d223575 q = 1) : d225487 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d223575, d225487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d223575, d225487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d223576 q = 1) : d225488 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d223576, d225488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d223576, d225488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro22262 (p : Pattern) (selected : d223582 p = 1) : d225494 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223577 q = 1) : d225489 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d223577, d225489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223577, d225489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22261 q selected
  have h2 (q : Pattern) (selected : d223578 q = 1) : d225490 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d223578, d225490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223578, d225490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223579 q = 1) : d225491 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d223579, d225491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223579, d225491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223580 q = 1) : d225492 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d223580, d225492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223580, d225492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223581 q = 1) : d225493 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d223581, d225493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223581, d225493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223582 q = 1) : d225494 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d223582, d225494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223582, d225494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22263 (p : Pattern) (selected : d223687 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d118300 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9310 q selected
    | true =>
      simp only [d118300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118301 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118302 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118303 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223685 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118317 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9315 q selected
    | true =>
      simp only [d118317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118318 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d118319 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d118320 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d118320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d223686 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d223687 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22264 (p : Pattern) (selected : d223689 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d118304 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9311 q selected
    | true =>
      simp only [d118304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118305 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118306 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118307 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118317 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9315 q selected
    | true =>
      simp only [d118317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118318 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118319 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d118320 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d223688 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d118321 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d118321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d223689 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d223689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22265 (p : Pattern) (selected : d223693 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d118317 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9315 q selected
    | true =>
      simp only [d118317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118318 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118319 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118320 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118321 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223693 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22266 (p : Pattern) (selected : d223698 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d118309 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9313 q selected
    | true =>
      simp only [d118309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118310 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118311 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118312 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118326 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223698 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22267 (p : Pattern) (selected : d223704 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223690 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22263 q selected
    | true =>
      simp only [d223690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22264 q selected
  have h2 (q : Pattern) (selected : d223691 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223692 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223694 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22264 q selected
    | true =>
      simp only [d223694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22265 q selected
  have h5 (q : Pattern) (selected : d223695 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223696 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223697 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223699 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22264 q selected
    | true =>
      simp only [d223699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22266 q selected
  have h9 (q : Pattern) (selected : d223700 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d223701 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d223702 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d223702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d223703 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d223703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d223704 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d223704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d223704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro22268 (p : Pattern) (selected : d223708 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223699 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22264 q selected
    | true =>
      simp only [d223699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22266 q selected
  have h2 (q : Pattern) (selected : d223700 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223701 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223702 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223707 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d223707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223708 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d223708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22269 (p : Pattern) (selected : d223714 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223705 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22267 q selected
    | true =>
      simp only [d223705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223706 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223709 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22268 q selected
    | true =>
      simp only [d223709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223710 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223711 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223712 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223713 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223714 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22270 (p : Pattern) (selected : d223718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223709 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22268 q selected
    | true =>
      simp only [d223709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223710 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223715 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223716 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223717 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223718 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22271 (p : Pattern) (selected : d223730 p = 1) : d225503 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223647 q = 1) : d223647 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d223656 q = 1) : d223656 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d223684 q = 1) : d223684 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d223719 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22269 q selected
    | true =>
      simp only [d223719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22270 q selected
  have h5 (q : Pattern) (selected : d223720 q = 1) : d225499 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223720, d225499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223720, d225499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223726 q = 1) : d223726 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d223727 q = 1) : d225500 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223727, d225500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223727, d225500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223728 q = 1) : d225501 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223728, d225501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223728, d225501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d223729 q = 1) : d225502 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d223729, d225502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223729, d225502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d223730 q = 1) : d225503 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d223730, d225503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223730, d225503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro22272 (p : Pattern) (selected : d223745 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223705 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22267 q selected
    | true =>
      simp only [d223705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223706 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223709 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22268 q selected
    | true =>
      simp only [d223709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223710 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223711 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223712 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223713 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223745 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22273 (p : Pattern) (selected : d223746 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223709 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22268 q selected
    | true =>
      simp only [d223709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223710 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223715 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223716 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223717 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223746 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22274 (p : Pattern) (selected : d223755 p = 1) : d225508 p = 1 := by
  have h0 (q : Pattern) (selected : d223647 q = 1) : d223647 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223656 q = 1) : d223656 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d223684 q = 1) : d223684 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d223719 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22269 q selected
    | true =>
      simp only [d223719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22270 q selected
  have h4 (q : Pattern) (selected : d223720 q = 1) : d225499 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223720, d225499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223720, d225499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223726 q = 1) : d223726 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d223727 q = 1) : d225500 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223727, d225500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223727, d225500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223728 q = 1) : d225501 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223728, d225501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223728, d225501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223729 q = 1) : d225502 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d223729, d225502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223729, d225502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d223736 q = 1) : d223736 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d223741 q = 1) : d223741 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d223744 q = 1) : d223744 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d223747 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22272 q selected
    | true =>
      simp only [d223747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22273 q selected
  have h13 (q : Pattern) (selected : d223748 q = 1) : d225504 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223748, d225504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d223748, d225504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d223751 q = 1) : d223751 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d223752 q = 1) : d225505 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223752, d225505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d223752, d225505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d223753 q = 1) : d225506 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223753, d225506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d223753, d225506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d223754 q = 1) : d225507 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d223754, d225507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d223754, d225507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d223755 q = 1) : d225508 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d223755, d225508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d223755, d225508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro22275 (p : Pattern) (selected : d223780 p = 1) : d225515 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223744 q = 1) : d223744 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d223747 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22272 q selected
    | true =>
      simp only [d223747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22273 q selected
  have h3 (q : Pattern) (selected : d223748 q = 1) : d225504 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223748, d225504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223748, d225504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223751 q = 1) : d223751 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d223752 q = 1) : d225505 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223752, d225505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223752, d225505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223778 q = 1) : d225513 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223778, d225513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223778, d225513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223779 q = 1) : d225514 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d223779, d225514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223779, d225514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223780 q = 1) : d225515 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d223780, d225515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223780, d225515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22276 (p : Pattern) (selected : d223840 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d118481 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9310 q selected
  have h2 (q : Pattern) (selected : d118300 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9310 q selected
    | true =>
      simp only [d118300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118482 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118301 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118483 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118484 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223838 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d118498 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9315 q selected
  have h9 (q : Pattern) (selected : d118317 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9315 q selected
    | true =>
      simp only [d118317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d118499 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d118499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d118318 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d118318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d118500 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d118500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d118501 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d118501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d223839 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d223840 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22277 (p : Pattern) (selected : d223842 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d118485 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9311 q selected
  have h2 (q : Pattern) (selected : d118304 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9311 q selected
    | true =>
      simp only [d118304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118486 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118305 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118487 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118488 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118498 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9315 q selected
  have h8 (q : Pattern) (selected : d118317 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9315 q selected
    | true =>
      simp only [d118317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d118499 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d118318 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d118318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d118500 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d118500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d118501 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d118501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d223841 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d118502 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d118502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d223842 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d223842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22278 (p : Pattern) (selected : d223846 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d118498 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9315 q selected
  have h2 (q : Pattern) (selected : d118317 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9315 q selected
    | true =>
      simp only [d118317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118499 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118318 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118500 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118501 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118502 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223846 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22279 (p : Pattern) (selected : d223851 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d118490 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9313 q selected
  have h2 (q : Pattern) (selected : d118309 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9313 q selected
    | true =>
      simp only [d118309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118491 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118310 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118492 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118493 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118507 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223851 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22280 (p : Pattern) (selected : d223857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223843 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22276 q selected
    | true =>
      simp only [d223843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22277 q selected
  have h2 (q : Pattern) (selected : d223844 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223845 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223847 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22277 q selected
    | true =>
      simp only [d223847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22278 q selected
  have h5 (q : Pattern) (selected : d223848 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223849 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223850 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223852 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22277 q selected
    | true =>
      simp only [d223852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22279 q selected
  have h9 (q : Pattern) (selected : d223853 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d223854 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d223855 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d223855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d223856 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d223856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d223857 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d223857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d223857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro22281 (p : Pattern) (selected : d223861 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223852 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22277 q selected
    | true =>
      simp only [d223852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22279 q selected
  have h2 (q : Pattern) (selected : d223853 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223854 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223855 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223860 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d223860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223861 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d223861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22282 (p : Pattern) (selected : d223867 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223858 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22280 q selected
    | true =>
      simp only [d223858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223859 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223862 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22281 q selected
    | true =>
      simp only [d223862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223863 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223864 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223865 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223866 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223867 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22283 (p : Pattern) (selected : d223871 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223862 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22281 q selected
    | true =>
      simp only [d223862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223863 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223868 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223869 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223870 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223871 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22284 (p : Pattern) (selected : d223887 p = 1) : d225525 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223837 q = 1) : d223837 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d223872 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22282 q selected
    | true =>
      simp only [d223872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22283 q selected
  have h3 (q : Pattern) (selected : d223873 q = 1) : d225521 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223873, d225521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223873, d225521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223883 q = 1) : d223883 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d223884 q = 1) : d225522 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223884, d225522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223884, d225522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223885 q = 1) : d225523 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223885, d225523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223885, d225523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223886 q = 1) : d225524 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d223886, d225524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223886, d225524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223887 q = 1) : d225525 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d223887, d225525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223887, d225525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22285 (p : Pattern) (selected : d223904 p = 1) : d225531 p = 1 := by
  have h0 (q : Pattern) (selected : d223639 q = 1) : d223639 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223756 q = 1) : d225509 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d223756, d225509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22271 q selected
    | true =>
      simp only [d223756, d225509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22274 q selected
  have h2 (q : Pattern) (selected : d223774 q = 1) : d223774 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d223775 q = 1) : d225510 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d223775, d225510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223775, d225510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d223776 q = 1) : d225511 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d223776, d225511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223776, d225511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223777 q = 1) : d225512 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d223777, d225512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223777, d225512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223781 q = 1) : d225516 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d223781, d225516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223781, d225516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22275 q selected
  have h8 (q : Pattern) (selected : d223783 q = 1) : d223783 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d223784 q = 1) : d225517 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d223784, d225517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223784, d225517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d223785 q = 1) : d225518 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d223785, d225518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d223785, d225518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d223786 q = 1) : d225519 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d223786, d225519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d223786, d225519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d223787 q = 1) : d225520 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d223787, d225520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223787, d225520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d223888 q = 1) : d225526 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d223888, d225526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223888, d225526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22284 q selected
  have h14 (q : Pattern) (selected : d223899 q = 1) : d223899 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d223900 q = 1) : d225527 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d223900, d225527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d223900, d225527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d223901 q = 1) : d225528 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d223901, d225528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d223901, d225528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d223902 q = 1) : d225529 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d223902, d225529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d223902, d225529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d223903 q = 1) : d225530 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d223903, d225530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d223903, d225530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d223904 q = 1) : d225531 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d223904, d225531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d223904, d225531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro22286 (p : Pattern) (selected : d223910 p = 1) : d225537 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223905 q = 1) : d225532 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d223905, d225532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223905, d225532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22285 q selected
  have h2 (q : Pattern) (selected : d223906 q = 1) : d225533 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d223906, d225533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223906, d225533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223907 q = 1) : d225534 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d223907, d225534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223907, d225534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223908 q = 1) : d225535 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d223908, d225535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223908, d225535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223909 q = 1) : d225536 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d223909, d225536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223909, d225536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223910 q = 1) : d225537 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d223910, d225537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223910, d225537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22287 (p : Pattern) (selected : d223916 p = 1) : d225543 p = 1 := by
  have h0 (q : Pattern) (selected : d222647 q = 1) : d225372 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d222647, d225372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22180 q selected
    | true =>
      simp only [d222647, d225372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22193 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d222942 q = 1) : d225412 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d222942, d225412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d222942, d225412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22214 q selected
  have h3 (q : Pattern) (selected : d222943 q = 1) : d225413 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d222943, d225413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222943, d225413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223246 q = 1) : d225453 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d223246, d225453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223246, d225453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22237 q selected
  have h5 (q : Pattern) (selected : d223247 q = 1) : d225454 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d223247, d225454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223247, d225454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223248 q = 1) : d225455 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d223248, d225455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223248, d225455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223583 q = 1) : d225495 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d223583, d225495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223583, d225495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22262 q selected
  have h8 (q : Pattern) (selected : d223584 q = 1) : d225496 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d223584, d225496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223584, d225496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d223585 q = 1) : d225497 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d223585, d225497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223585, d225497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d223586 q = 1) : d225498 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d223586, d225498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223586, d225498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d223911 q = 1) : d225538 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d223911, d225538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223911, d225538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22286 q selected
  have h12 (q : Pattern) (selected : d223912 q = 1) : d225539 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d223912, d225539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223912, d225539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d223913 q = 1) : d225540 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d223913, d225540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223913, d225540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d223914 q = 1) : d225541 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d223914, d225541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223914, d225541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d223915 q = 1) : d225542 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d223915, d225542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d223915, d225542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d223916 q = 1) : d225543 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d223916, d225543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d223916, d225543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro22288 (p : Pattern) (selected : d223922 p = 1) : d225549 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223917 q = 1) : d225544 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d223917, d225544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22287 q selected
    | true =>
      simp only [d223917, d225544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223918 q = 1) : d225545 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d223918, d225545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223918, d225545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d223919 q = 1) : d225546 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d223919, d225546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223919, d225546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223920 q = 1) : d225547 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d223920, d225547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223920, d225547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223921 q = 1) : d225548 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d223921, d225548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223921, d225548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223922 q = 1) : d225549 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d223922, d225549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223922, d225549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22289 (p : Pattern) (selected : d223928 p = 1) : d225555 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223923 q = 1) : d225550 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d223923, d225550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22288 q selected
    | true =>
      simp only [d223923, d225550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223924 q = 1) : d225551 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d223924, d225551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223924, d225551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d223925 q = 1) : d225552 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d223925, d225552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223925, d225552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223926 q = 1) : d225553 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d223926, d225553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223926, d225553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223927 q = 1) : d225554 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d223927, d225554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223927, d225554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223928 q = 1) : d225555 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d223928, d225555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223928, d225555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22290 (p : Pattern) (selected : d223933 p = 1) : d225560 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223929 q = 1) : d225556 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d223929, d225556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22289 q selected
    | true =>
      simp only [d223929, d225556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223930 q = 1) : d225557 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d223930, d225557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223930, d225557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d223931 q = 1) : d225558 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d223931, d225558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223931, d225558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223932 q = 1) : d225559 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d223932, d225559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223932, d225559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223933 q = 1) : d225560 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d223933, d225560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223933, d225560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro22291 (p : Pattern) (selected : d223939 p = 1) : d225566 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223934 q = 1) : d225561 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d223934, d225561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22290 q selected
    | true =>
      simp only [d223934, d225561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223935 q = 1) : d225562 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d223935, d225562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223935, d225562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d223936 q = 1) : d225563 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d223936, d225563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223936, d225563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223937 q = 1) : d225564 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d223937, d225564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223937, d225564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223938 q = 1) : d225565 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d223938, d225565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223938, d225565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223939 q = 1) : d225566 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d223939, d225566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223939, d225566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22292 (p : Pattern) (selected : d223945 p = 1) : d225572 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223940 q = 1) : d225567 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d223940, d225567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22291 q selected
    | true =>
      simp only [d223940, d225567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223941 q = 1) : d225568 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d223941, d225568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223941, d225568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d223942 q = 1) : d225569 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d223942, d225569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223942, d225569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223943 q = 1) : d225570 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d223943, d225570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223943, d225570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223944 q = 1) : d225571 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d223944, d225571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223944, d225571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223945 q = 1) : d225572 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d223945, d225572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223945, d225572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22293 (p : Pattern) (selected : d223951 p = 1) : d225578 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223946 q = 1) : d225573 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d223946, d225573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22292 q selected
    | true =>
      simp only [d223946, d225573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223947 q = 1) : d225574 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d223947, d225574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223947, d225574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d223948 q = 1) : d225575 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d223948, d225575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223948, d225575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223949 q = 1) : d225576 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d223949, d225576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223949, d225576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223950 q = 1) : d225577 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d223950, d225577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223950, d225577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223951 q = 1) : d225578 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d223951, d225578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223951, d225578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22294 (p : Pattern) (selected : d223957 p = 1) : d225584 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223952 q = 1) : d225579 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d223952, d225579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22293 q selected
    | true =>
      simp only [d223952, d225579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223953 q = 1) : d225580 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d223953, d225580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223953, d225580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d223954 q = 1) : d225581 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d223954, d225581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223954, d225581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223955 q = 1) : d225582 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d223955, d225582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223955, d225582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223956 q = 1) : d225583 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d223956, d225583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223956, d225583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223957 q = 1) : d225584 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d223957, d225584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223957, d225584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22295 (p : Pattern) (selected : d225620 p = 0) : d226714 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225615 q = 0) : d226709 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225615, d226709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225615, d226709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro187 q selected
  have h2 (q : Pattern) (selected : d225616 q = 0) : d226710 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225616, d226710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro187 q selected
    | true =>
      simp only [d225616, d226710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d225617 q = 0) : d226711 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225617, d226711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d225617, d226711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d225618 q = 0) : d226712 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225618, d226712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225618, d226712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225619 q = 0) : d226713 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d225619, d226713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225619, d226713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d225620 q = 0) : d226714 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d225620, d226714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225620, d226714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22296 (p : Pattern) (selected : d225625 p = 0) : d226719 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225621 q = 0) : d226715 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d225621, d226715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22295 q selected
    | true =>
      simp only [d225621, d226715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d225622 q = 0) : d226716 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d225622, d226716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225622, d226716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d225623 q = 0) : d226717 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d225623, d226717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d225623, d226717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d225624 q = 0) : d226718 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d225624, d226718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225624, d226718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225625 q = 0) : d226719 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d225625, d226719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225625, d226719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro22297 (p : Pattern) (selected : d225631 p = 0) : d226725 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225626 q = 0) : d226720 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d225626, d226720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22296 q selected
    | true =>
      simp only [d225626, d226720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d225627 q = 0) : d226721 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d225627, d226721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225627, d226721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d225628 q = 0) : d226722 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d225628, d226722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d225628, d226722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d225629 q = 0) : d226723 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d225629, d226723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225629, d226723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225630 q = 0) : d226724 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d225630, d226724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225630, d226724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d225631 q = 0) : d226725 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d225631, d226725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225631, d226725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22298 (p : Pattern) (selected : d225637 p = 0) : d226731 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225632 q = 0) : d226726 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d225632, d226726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22297 q selected
    | true =>
      simp only [d225632, d226726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d225633 q = 0) : d226727 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d225633, d226727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d225633, d226727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d225634 q = 0) : d226728 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d225634, d226728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d225634, d226728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d225635 q = 0) : d226729 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d225635, d226729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225635, d226729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d225636 q = 0) : d226730 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d225636, d226730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225636, d226730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d225637 q = 0) : d226731 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d225637, d226731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225637, d226731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22299 (p : Pattern) (selected : d225643 p = 0) : d226737 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225638 q = 0) : d226732 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d225638, d226732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225638, d226732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22298 q selected
  have h2 (q : Pattern) (selected : d225639 q = 0) : d226733 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d225639, d226733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d225639, d226733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d225640 q = 0) : d226734 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d225640, d226734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d225640, d226734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d225641 q = 0) : d226735 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d225641, d226735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225641, d226735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225642 q = 0) : d226736 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d225642, d226736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225642, d226736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d225643 q = 0) : d226737 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d225643, d226737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225643, d226737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22300 (p : Pattern) (selected : d225653 p = 0) : d226747 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225648 q = 0) : d226742 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225648, d226742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225648, d226742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro205 q selected
  have h2 (q : Pattern) (selected : d225649 q = 0) : d226743 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225649, d226743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro205 q selected
    | true =>
      simp only [d225649, d226743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d225650 q = 0) : d226744 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225650, d226744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d225650, d226744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d225651 q = 0) : d226745 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225651, d226745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225651, d226745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225615 q = 0) : d226709 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225615, d226709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225615, d226709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro187 q selected
  have h6 (q : Pattern) (selected : d225616 q = 0) : d226710 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225616, d226710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro187 q selected
    | true =>
      simp only [d225616, d226710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d225617 q = 0) : d226711 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225617, d226711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225617, d226711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d225618 q = 0) : d226712 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225618, d226712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d225618, d226712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d225652 q = 0) : d226746 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d225652, d226746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225652, d226746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d225619 q = 0) : d226713 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d225619, d226713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d225619, d226713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d225653 q = 0) : d226747 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d225653, d226747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d225653, d226747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22301 (p : Pattern) (selected : d225658 p = 0) : d226752 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225654 q = 0) : d226748 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d225654, d226748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22300 q selected
    | true =>
      simp only [d225654, d226748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22295 q selected
  have h2 (q : Pattern) (selected : d225655 q = 0) : d226749 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d225655, d226749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225655, d226749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d225621 q = 0) : d226715 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d225621, d226715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22295 q selected
    | true =>
      simp only [d225621, d226715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d225622 q = 0) : d226716 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d225622, d226716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225622, d226716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d225656 q = 0) : d226750 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d225656, d226750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d225656, d226750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d225623 q = 0) : d226717 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d225623, d226717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225623, d226717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d225657 q = 0) : d226751 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d225657, d226751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225657, d226751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d225658 q = 0) : d226752 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d225658, d226752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d225658, d226752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22302 (p : Pattern) (selected : d225664 p = 0) : d226758 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225659 q = 0) : d226753 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d225659, d226753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22301 q selected
    | true =>
      simp only [d225659, d226753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d225660 q = 0) : d226754 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d225660, d226754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225660, d226754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d225626 q = 0) : d226720 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d225626, d226720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22296 q selected
    | true =>
      simp only [d225626, d226720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d225627 q = 0) : d226721 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d225627, d226721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225627, d226721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d225661 q = 0) : d226755 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d225661, d226755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d225661, d226755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d225662 q = 0) : d226756 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d225662, d226756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225662, d226756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d225663 q = 0) : d226757 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d225663, d226757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d225663, d226757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d225664 q = 0) : d226758 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d225664, d226758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d225664, d226758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22303 (p : Pattern) (selected : d225671 p = 0) : d226714 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225666 q = 0) : d226709 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225666, d226709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225666, d226709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro210 q selected
  have h2 (q : Pattern) (selected : d225667 q = 0) : d226710 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225667, d226710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro210 q selected
    | true =>
      simp only [d225667, d226710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d225668 q = 0) : d226711 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225668, d226711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d225668, d226711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d225669 q = 0) : d226712 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225669, d226712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225669, d226712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225670 q = 0) : d226713 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d225670, d226713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225670, d226713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d225671 q = 0) : d226714 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d225671, d226714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225671, d226714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22304 (p : Pattern) (selected : d225676 p = 0) : d226719 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225672 q = 0) : d226715 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d225672, d226715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22303 q selected
    | true =>
      simp only [d225672, d226715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d225673 q = 0) : d226716 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d225673, d226716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225673, d226716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d225674 q = 0) : d226717 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d225674, d226717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d225674, d226717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d225675 q = 0) : d226718 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d225675, d226718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225675, d226718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225676 q = 0) : d226719 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d225676, d226719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225676, d226719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro22305 (p : Pattern) (selected : d225682 p = 0) : d226725 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225677 q = 0) : d226720 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d225677, d226720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22304 q selected
    | true =>
      simp only [d225677, d226720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d225678 q = 0) : d226721 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d225678, d226721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225678, d226721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d225679 q = 0) : d226722 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d225679, d226722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d225679, d226722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d225680 q = 0) : d226723 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d225680, d226723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225680, d226723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225681 q = 0) : d226724 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d225681, d226724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225681, d226724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d225682 q = 0) : d226725 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d225682, d226725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225682, d226725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22306 (p : Pattern) (selected : d225688 p = 0) : d226764 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225665 q = 0) : d226759 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d225665, d226759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22302 q selected
    | true =>
      simp only [d225665, d226759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22297 q selected
  have h2 (q : Pattern) (selected : d225683 q = 0) : d226726 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d225683, d226726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22305 q selected
    | true =>
      simp only [d225683, d226726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d225684 q = 0) : d226760 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d225684, d226760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d225684, d226760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d225632 q = 0) : d226726 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d225632, d226726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22297 q selected
    | true =>
      simp only [d225632, d226726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225633 q = 0) : d226727 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d225633, d226727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225633, d226727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d225685 q = 0) : d226761 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d225685, d226761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225685, d226761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d225686 q = 0) : d226762 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d225686, d226762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225686, d226762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d225687 q = 0) : d226763 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d225687, d226763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225687, d226763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d225688 q = 0) : d226764 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d225688, d226764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225688, d226764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro22307 (p : Pattern) (selected : d225694 p = 0) : d226770 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225689 q = 0) : d226765 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d225689, d226765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225689, d226765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22306 q selected
  have h2 (q : Pattern) (selected : d225690 q = 0) : d226766 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d225690, d226766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d225690, d226766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d225691 q = 0) : d226767 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d225691, d226767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d225691, d226767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d225692 q = 0) : d226768 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d225692, d226768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225692, d226768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225693 q = 0) : d226769 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d225693, d226769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225693, d226769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d225694 q = 0) : d226770 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d225694, d226770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225694, d226770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22308 (p : Pattern) (selected : d225710 p = 0) : d226786 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225700 q = 0) : d226776 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225700, d226776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225700, d226776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro235 q selected
  have h2 (q : Pattern) (selected : d225701 q = 0) : d226777 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225701, d226777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro235 q selected
    | true =>
      simp only [d225701, d226777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d225702 q = 0) : d226778 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225702, d226778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d225702, d226778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d225703 q = 0) : d226779 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225703, d226779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225703, d226779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225648 q = 0) : d226742 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225648, d226742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225648, d226742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro205 q selected
  have h6 (q : Pattern) (selected : d225649 q = 0) : d226743 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225649, d226743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro205 q selected
    | true =>
      simp only [d225649, d226743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d225650 q = 0) : d226744 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225650, d226744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225650, d226744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d225651 q = 0) : d226745 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225651, d226745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d225651, d226745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d225704 q = 0) : d226780 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d225704, d226780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225704, d226780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d225705 q = 0) : d226781 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225705, d226781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225705, d226781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6607 q selected
  have h11 (q : Pattern) (selected : d225706 q = 0) : d226782 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225706, d226782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6607 q selected
    | true =>
      simp only [d225706, d226782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d225707 q = 0) : d226783 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225707, d226783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d225707, d226783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d225708 q = 0) : d226784 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225708, d226784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d225708, d226784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d225615 q = 0) : d226709 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225615, d226709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225615, d226709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro187 q selected
  have h15 (q : Pattern) (selected : d225616 q = 0) : d226710 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225616, d226710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro187 q selected
    | true =>
      simp only [d225616, d226710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d225617 q = 0) : d226711 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225617, d226711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d225617, d226711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d225618 q = 0) : d226712 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225618, d226712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d225618, d226712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d225709 q = 0) : d226785 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d225709, d226785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d225709, d226785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d225710 q = 0) : d226786 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d225710, d226786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d225710, d226786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro22309 (p : Pattern) (selected : d225715 p = 0) : d226791 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225711 q = 0) : d226787 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d225711, d226787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22308 q selected
    | true =>
      simp only [d225711, d226787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22300 q selected
  have h2 (q : Pattern) (selected : d225712 q = 0) : d226788 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d225712, d226788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225712, d226788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d225654 q = 0) : d226748 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d225654, d226748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22300 q selected
    | true =>
      simp only [d225654, d226748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22295 q selected
  have h4 (q : Pattern) (selected : d225655 q = 0) : d226749 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d225655, d226749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225655, d226749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d225713 q = 0) : d226789 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d225713, d226789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d225713, d226789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d225621 q = 0) : d226715 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d225621, d226715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22295 q selected
    | true =>
      simp only [d225621, d226715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d225622 q = 0) : d226716 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d225622, d226716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225622, d226716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d225656 q = 0) : d226750 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d225656, d226750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225656, d226750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d225714 q = 0) : d226790 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d225714, d226790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225714, d226790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d225715 q = 0) : d226791 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d225715, d226791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d225715, d226791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22310 (p : Pattern) (selected : d225721 p = 0) : d226797 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225716 q = 0) : d226792 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d225716, d226792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22309 q selected
    | true =>
      simp only [d225716, d226792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d225717 q = 0) : d226793 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d225717, d226793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225717, d226793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d225659 q = 0) : d226753 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d225659, d226753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22301 q selected
    | true =>
      simp only [d225659, d226753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d225660 q = 0) : d226754 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d225660, d226754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225660, d226754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d225718 q = 0) : d226794 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d225718, d226794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d225718, d226794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d225719 q = 0) : d226795 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d225719, d226795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225719, d226795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d225720 q = 0) : d226796 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d225720, d226796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d225720, d226796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d225721 q = 0) : d226797 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d225721, d226797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d225721, d226797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22311 (p : Pattern) (selected : d225728 p = 0) : d226747 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225723 q = 0) : d226742 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225723, d226742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225723, d226742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro240 q selected
  have h2 (q : Pattern) (selected : d225724 q = 0) : d226743 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225724, d226743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro240 q selected
    | true =>
      simp only [d225724, d226743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d225725 q = 0) : d226744 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225725, d226744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d225725, d226744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d225726 q = 0) : d226745 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225726, d226745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225726, d226745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225666 q = 0) : d226709 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225666, d226709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225666, d226709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro210 q selected
  have h6 (q : Pattern) (selected : d225667 q = 0) : d226710 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225667, d226710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro210 q selected
    | true =>
      simp only [d225667, d226710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d225668 q = 0) : d226711 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225668, d226711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225668, d226711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d225669 q = 0) : d226712 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225669, d226712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d225669, d226712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d225727 q = 0) : d226746 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d225727, d226746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225727, d226746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d225670 q = 0) : d226713 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d225670, d226713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d225670, d226713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d225728 q = 0) : d226747 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d225728, d226747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d225728, d226747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22312 (p : Pattern) (selected : d225733 p = 0) : d226752 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225729 q = 0) : d226748 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d225729, d226748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22311 q selected
    | true =>
      simp only [d225729, d226748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22303 q selected
  have h2 (q : Pattern) (selected : d225730 q = 0) : d226749 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d225730, d226749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225730, d226749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d225672 q = 0) : d226715 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d225672, d226715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22303 q selected
    | true =>
      simp only [d225672, d226715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d225673 q = 0) : d226716 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d225673, d226716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225673, d226716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d225731 q = 0) : d226750 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d225731, d226750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d225731, d226750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d225674 q = 0) : d226717 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d225674, d226717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225674, d226717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d225732 q = 0) : d226751 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d225732, d226751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225732, d226751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d225733 q = 0) : d226752 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d225733, d226752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d225733, d226752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22313 (p : Pattern) (selected : d225739 p = 0) : d226758 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225734 q = 0) : d226753 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d225734, d226753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22312 q selected
    | true =>
      simp only [d225734, d226753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d225735 q = 0) : d226754 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d225735, d226754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225735, d226754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d225677 q = 0) : d226720 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d225677, d226720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22304 q selected
    | true =>
      simp only [d225677, d226720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d225678 q = 0) : d226721 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d225678, d226721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225678, d226721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d225736 q = 0) : d226755 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d225736, d226755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d225736, d226755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d225737 q = 0) : d226756 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d225737, d226756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225737, d226756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d225738 q = 0) : d226757 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d225738, d226757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d225738, d226757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d225739 q = 0) : d226758 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d225739, d226758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d225739, d226758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22314 (p : Pattern) (selected : d225745 p = 0) : d226803 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225659 q = 0) : d226753 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d225659, d226753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22301 q selected
    | true =>
      simp only [d225659, d226753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d225660 q = 0) : d226754 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d225660, d226754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225660, d226754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d225742 q = 0) : d226800 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d225742, d226800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d225742, d226800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d225743 q = 0) : d226801 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d225743, d226801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225743, d226801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225744 q = 0) : d226802 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d225744, d226802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225744, d226802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d225745 q = 0) : d226803 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d225745, d226803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225745, d226803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22315 (p : Pattern) (selected : d225751 p = 0) : d226809 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225722 q = 0) : d226798 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d225722, d226798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22310 q selected
    | true =>
      simp only [d225722, d226798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22302 q selected
  have h2 (q : Pattern) (selected : d225740 q = 0) : d226759 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d225740, d226759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22313 q selected
    | true =>
      simp only [d225740, d226759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22305 q selected
  have h3 (q : Pattern) (selected : d225741 q = 0) : d226799 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d225741, d226799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d225741, d226799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d225746 q = 0) : d226804 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d225746, d226804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22314 q selected
    | true =>
      simp only [d225746, d226804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225747 q = 0) : d226805 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d225747, d226805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225747, d226805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d225748 q = 0) : d226806 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d225748, d226806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225748, d226806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d225749 q = 0) : d226807 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d225749, d226807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225749, d226807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d225750 q = 0) : d226808 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d225750, d226808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225750, d226808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d225751 q = 0) : d226809 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d225751, d226809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225751, d226809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro22316 (p : Pattern) (selected : d225757 p = 0) : d226815 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225632 q = 0) : d226726 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d225632, d226726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22297 q selected
    | true =>
      simp only [d225632, d226726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d225753 q = 0) : d226811 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d225753, d226811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225753, d226811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d225754 q = 0) : d226812 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d225754, d226812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d225754, d226812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d225755 q = 0) : d226813 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d225755, d226813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225755, d226813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d225756 q = 0) : d226814 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d225756, d226814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225756, d226814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d225757 q = 0) : d226815 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d225757, d226815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225757, d226815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22317 (p : Pattern) (selected : d225763 p = 0) : d226821 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225752 q = 0) : d226810 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d225752, d226810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225752, d226810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22315 q selected
  have h2 (q : Pattern) (selected : d225758 q = 0) : d226816 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d225758, d226816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225758, d226816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22316 q selected
  have h3 (q : Pattern) (selected : d225759 q = 0) : d226817 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d225759, d226817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d225759, d226817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d225760 q = 0) : d226818 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d225760, d226818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225760, d226818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225761 q = 0) : d226819 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d225761, d226819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225761, d226819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d225762 q = 0) : d226820 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d225762, d226820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225762, d226820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d225763 q = 0) : d226821 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d225763, d226821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225763, d226821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro22318 (p : Pattern) (selected : d225769 p = 0) : d226827 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225644 q = 0) : d226738 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d225644, d226738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225644, d226738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22299 q selected
  have h2 (q : Pattern) (selected : d225645 q = 0) : d226739 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d225645, d226739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225645, d226739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d225646 q = 0) : d226740 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d225646, d226740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225646, d226740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d225647 q = 0) : d226741 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d225647, d226741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225647, d226741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d225695 q = 0) : d226771 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d225695, d226771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225695, d226771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22307 q selected
  have h6 (q : Pattern) (selected : d225696 q = 0) : d226772 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d225696, d226772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225696, d226772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d225697 q = 0) : d226773 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d225697, d226773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225697, d226773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d225698 q = 0) : d226774 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d225698, d226774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225698, d226774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d225699 q = 0) : d226775 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d225699, d226775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225699, d226775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d225764 q = 0) : d226822 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d225764, d226822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225764, d226822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22317 q selected
  have h11 (q : Pattern) (selected : d225765 q = 0) : d226823 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d225765, d226823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225765, d226823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d225766 q = 0) : d226824 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d225766, d226824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225766, d226824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d225767 q = 0) : d226825 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d225767, d226825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225767, d226825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d225768 q = 0) : d226826 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d225768, d226826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225768, d226826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d225769 q = 0) : d226827 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d225769, d226827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d225769, d226827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22319 (p : Pattern) (selected : d225784 p = 0) : d226842 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225770 q = 0) : d226828 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225770, d226828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225770, d226828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro277 q selected
  have h2 (q : Pattern) (selected : d225771 q = 0) : d226829 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225771, d226829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro277 q selected
    | true =>
      simp only [d225771, d226829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d225772 q = 0) : d226830 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225772, d226830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d225772, d226830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d225773 q = 0) : d226831 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225773, d226831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225773, d226831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225774 q = 0) : d226832 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225774, d226832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225774, d226832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6619 q selected
  have h6 (q : Pattern) (selected : d225775 q = 0) : d226833 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225775, d226833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6619 q selected
    | true =>
      simp only [d225775, d226833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d225776 q = 0) : d226834 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225776, d226834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225776, d226834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d225777 q = 0) : d226835 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225777, d226835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d225777, d226835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d225778 q = 0) : d226836 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d225778, d226836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225778, d226836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d225779 q = 0) : d226837 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225779, d226837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225779, d226837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6620 q selected
  have h11 (q : Pattern) (selected : d225780 q = 0) : d226838 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225780, d226838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6620 q selected
    | true =>
      simp only [d225780, d226838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d225781 q = 0) : d226839 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225781, d226839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d225781, d226839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d225782 q = 0) : d226840 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225782, d226840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d225782, d226840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d225705 q = 0) : d226781 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225705, d226781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225705, d226781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6607 q selected
  have h15 (q : Pattern) (selected : d225706 q = 0) : d226782 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225706, d226782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6607 q selected
    | true =>
      simp only [d225706, d226782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d225707 q = 0) : d226783 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225707, d226783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d225707, d226783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d225708 q = 0) : d226784 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225708, d226784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d225708, d226784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d225783 q = 0) : d226841 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d225783, d226841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d225783, d226841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d225784 q = 0) : d226842 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d225784, d226842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d225784, d226842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro22320 (p : Pattern) (selected : d225787 p = 0) : d226845 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225705 q = 0) : d226781 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225705, d226781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225705, d226781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6607 q selected
  have h2 (q : Pattern) (selected : d225706 q = 0) : d226782 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225706, d226782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6607 q selected
    | true =>
      simp only [d225706, d226782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d225707 q = 0) : d226783 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225707, d226783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d225707, d226783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d225708 q = 0) : d226784 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225708, d226784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225708, d226784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225615 q = 0) : d226709 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225615, d226709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225615, d226709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro187 q selected
  have h6 (q : Pattern) (selected : d225616 q = 0) : d226710 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225616, d226710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro187 q selected
    | true =>
      simp only [d225616, d226710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d225617 q = 0) : d226711 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225617, d226711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225617, d226711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d225618 q = 0) : d226712 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225618, d226712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d225618, d226712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d225709 q = 0) : d226785 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d225709, d226785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225709, d226785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d225619 q = 0) : d226713 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d225619, d226713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d225619, d226713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d225787 q = 0) : d226845 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d225787, d226845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d225787, d226845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22321 (p : Pattern) (selected : d225792 p = 0) : d226850 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225785 q = 0) : d226843 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d225785, d226843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22319 q selected
    | true =>
      simp only [d225785, d226843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22308 q selected
  have h2 (q : Pattern) (selected : d225786 q = 0) : d226844 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d225786, d226844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225786, d226844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d225788 q = 0) : d226846 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d225788, d226846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22308 q selected
    | true =>
      simp only [d225788, d226846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22320 q selected
  have h4 (q : Pattern) (selected : d225789 q = 0) : d226847 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d225789, d226847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225789, d226847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d225790 q = 0) : d226848 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d225790, d226848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d225790, d226848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d225711 q = 0) : d226787 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d225711, d226787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22308 q selected
    | true =>
      simp only [d225711, d226787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22300 q selected
  have h7 (q : Pattern) (selected : d225712 q = 0) : d226788 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d225712, d226788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225712, d226788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d225654 q = 0) : d226748 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d225654, d226748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22300 q selected
    | true =>
      simp only [d225654, d226748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22295 q selected
  have h9 (q : Pattern) (selected : d225655 q = 0) : d226749 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d225655, d226749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225655, d226749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d225713 q = 0) : d226789 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d225713, d226789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d225713, d226789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d225791 q = 0) : d226849 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d225791, d226849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225791, d226849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d225792 q = 0) : d226850 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d225792, d226850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d225792, d226850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h12 p selected
theorem eqIntro22322 (p : Pattern) (selected : d225797 p = 0) : d226855 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225711 q = 0) : d226787 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d225711, d226787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22308 q selected
    | true =>
      simp only [d225711, d226787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22300 q selected
  have h2 (q : Pattern) (selected : d225712 q = 0) : d226788 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d225712, d226788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225712, d226788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d225654 q = 0) : d226748 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d225654, d226748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22300 q selected
    | true =>
      simp only [d225654, d226748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22295 q selected
  have h4 (q : Pattern) (selected : d225655 q = 0) : d226749 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d225655, d226749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225655, d226749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d225713 q = 0) : d226789 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d225713, d226789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d225713, d226789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d225795 q = 0) : d226853 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d225795, d226853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225795, d226853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d225796 q = 0) : d226854 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d225796, d226854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225796, d226854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d225797 q = 0) : d226855 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d225797, d226855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d225797, d226855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22323 (p : Pattern) (selected : d225803 p = 0) : d226861 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225793 q = 0) : d226851 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d225793, d226851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22321 q selected
    | true =>
      simp only [d225793, d226851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d225794 q = 0) : d226852 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d225794, d226852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225794, d226852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d225798 q = 0) : d226856 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d225798, d226856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22322 q selected
    | true =>
      simp only [d225798, d226856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d225799 q = 0) : d226857 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d225799, d226857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225799, d226857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d225800 q = 0) : d226858 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d225800, d226858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d225800, d226858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d225801 q = 0) : d226859 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d225801, d226859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225801, d226859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d225802 q = 0) : d226860 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d225802, d226860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d225802, d226860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d225803 q = 0) : d226861 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d225803, d226861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d225803, d226861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22324 (p : Pattern) (selected : d225805 p = 0) : d226863 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225654 q = 0) : d226748 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d225654, d226748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22300 q selected
    | true =>
      simp only [d225654, d226748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22295 q selected
  have h2 (q : Pattern) (selected : d225655 q = 0) : d226749 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d225655, d226749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225655, d226749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d225795 q = 0) : d226853 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d225795, d226853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d225795, d226853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d225804 q = 0) : d226862 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d225804, d226862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225804, d226862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225805 q = 0) : d226863 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d225805, d226863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225805, d226863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro22325 (p : Pattern) (selected : d225811 p = 0) : d226869 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225798 q = 0) : d226856 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d225798, d226856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22322 q selected
    | true =>
      simp only [d225798, d226856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d225799 q = 0) : d226857 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d225799, d226857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225799, d226857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d225806 q = 0) : d226864 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d225806, d226864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22324 q selected
    | true =>
      simp only [d225806, d226864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d225807 q = 0) : d226865 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d225807, d226865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225807, d226865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d225808 q = 0) : d226866 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d225808, d226866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d225808, d226866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d225809 q = 0) : d226867 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d225809, d226867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225809, d226867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d225810 q = 0) : d226868 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d225810, d226868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d225810, d226868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d225811 q = 0) : d226869 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d225811, d226869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d225811, d226869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22326 (p : Pattern) (selected : d225823 p = 0) : d226786 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225813 q = 0) : d226776 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225813, d226776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225813, d226776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro282 q selected
  have h2 (q : Pattern) (selected : d225814 q = 0) : d226777 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225814, d226777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro282 q selected
    | true =>
      simp only [d225814, d226777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d225815 q = 0) : d226778 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225815, d226778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d225815, d226778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d225816 q = 0) : d226779 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225816, d226779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225816, d226779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225723 q = 0) : d226742 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225723, d226742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225723, d226742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro240 q selected
  have h6 (q : Pattern) (selected : d225724 q = 0) : d226743 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225724, d226743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro240 q selected
    | true =>
      simp only [d225724, d226743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d225725 q = 0) : d226744 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225725, d226744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225725, d226744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d225726 q = 0) : d226745 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225726, d226745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d225726, d226745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d225817 q = 0) : d226780 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d225817, d226780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225817, d226780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d225818 q = 0) : d226781 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225818, d226781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225818, d226781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6628 q selected
  have h11 (q : Pattern) (selected : d225819 q = 0) : d226782 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225819, d226782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6628 q selected
    | true =>
      simp only [d225819, d226782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d225820 q = 0) : d226783 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225820, d226783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d225820, d226783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d225821 q = 0) : d226784 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225821, d226784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d225821, d226784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d225666 q = 0) : d226709 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225666, d226709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225666, d226709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro210 q selected
  have h15 (q : Pattern) (selected : d225667 q = 0) : d226710 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225667, d226710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro210 q selected
    | true =>
      simp only [d225667, d226710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d225668 q = 0) : d226711 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225668, d226711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d225668, d226711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d225669 q = 0) : d226712 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225669, d226712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d225669, d226712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d225822 q = 0) : d226785 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d225822, d226785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d225822, d226785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d225823 q = 0) : d226786 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d225823, d226786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d225823, d226786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro22327 (p : Pattern) (selected : d225829 p = 0) : d226855 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225824 q = 0) : d226787 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d225824, d226787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22326 q selected
    | true =>
      simp only [d225824, d226787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22311 q selected
  have h2 (q : Pattern) (selected : d225825 q = 0) : d226788 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d225825, d226788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225825, d226788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d225729 q = 0) : d226748 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d225729, d226748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22311 q selected
    | true =>
      simp only [d225729, d226748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22303 q selected
  have h4 (q : Pattern) (selected : d225730 q = 0) : d226749 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d225730, d226749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225730, d226749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d225826 q = 0) : d226789 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d225826, d226789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d225826, d226789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d225827 q = 0) : d226853 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d225827, d226853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225827, d226853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d225828 q = 0) : d226854 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d225828, d226854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225828, d226854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d225829 q = 0) : d226855 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d225829, d226855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d225829, d226855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22328 (p : Pattern) (selected : d225833 p = 0) : d226863 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225729 q = 0) : d226748 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d225729, d226748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22311 q selected
    | true =>
      simp only [d225729, d226748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22303 q selected
  have h2 (q : Pattern) (selected : d225730 q = 0) : d226749 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d225730, d226749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225730, d226749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d225827 q = 0) : d226853 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d225827, d226853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d225827, d226853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d225832 q = 0) : d226862 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d225832, d226862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225832, d226862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225833 q = 0) : d226863 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d225833, d226863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225833, d226863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro22329 (p : Pattern) (selected : d225839 p = 0) : d226869 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225830 q = 0) : d226856 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d225830, d226856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22327 q selected
    | true =>
      simp only [d225830, d226856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d225831 q = 0) : d226857 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d225831, d226857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225831, d226857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d225834 q = 0) : d226864 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d225834, d226864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22328 q selected
    | true =>
      simp only [d225834, d226864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d225835 q = 0) : d226865 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d225835, d226865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225835, d226865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d225836 q = 0) : d226866 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d225836, d226866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d225836, d226866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d225837 q = 0) : d226867 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d225837, d226867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225837, d226867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d225838 q = 0) : d226868 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d225838, d226868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d225838, d226868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d225839 q = 0) : d226869 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d225839, d226869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d225839, d226869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22330 (p : Pattern) (selected : d225843 p = 0) : d226874 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225834 q = 0) : d226864 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d225834, d226864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22328 q selected
    | true =>
      simp only [d225834, d226864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d225835 q = 0) : d226865 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d225835, d226865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225835, d226865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d225840 q = 0) : d226871 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d225840, d226871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d225840, d226871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d225841 q = 0) : d226872 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d225841, d226872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225841, d226872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225842 q = 0) : d226873 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d225842, d226873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225842, d226873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d225843 q = 0) : d226874 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d225843, d226874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225843, d226874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22331 (p : Pattern) (selected : d225849 p = 0) : d226880 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225798 q = 0) : d226856 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d225798, d226856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22322 q selected
    | true =>
      simp only [d225798, d226856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d225799 q = 0) : d226857 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d225799, d226857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225799, d226857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d225846 q = 0) : d226877 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d225846, d226877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d225846, d226877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d225847 q = 0) : d226878 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d225847, d226878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225847, d226878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225848 q = 0) : d226879 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d225848, d226879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225848, d226879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d225849 q = 0) : d226880 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d225849, d226880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225849, d226880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22332 (p : Pattern) (selected : d225855 p = 0) : d226886 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225812 q = 0) : d226870 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d225812, d226870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22323 q selected
    | true =>
      simp only [d225812, d226870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22325 q selected
  have h2 (q : Pattern) (selected : d225844 q = 0) : d226875 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d225844, d226875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22329 q selected
    | true =>
      simp only [d225844, d226875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22330 q selected
  have h3 (q : Pattern) (selected : d225845 q = 0) : d226876 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d225845, d226876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d225845, d226876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d225850 q = 0) : d226881 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d225850, d226881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22331 q selected
    | true =>
      simp only [d225850, d226881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225851 q = 0) : d226882 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d225851, d226882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225851, d226882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d225852 q = 0) : d226883 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d225852, d226883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225852, d226883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d225853 q = 0) : d226884 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d225853, d226884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225853, d226884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d225854 q = 0) : d226885 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d225854, d226885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225854, d226885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d225855 q = 0) : d226886 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d225855, d226886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225855, d226886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro22333 (p : Pattern) (selected : d225860 p = 0) : d226874 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225806 q = 0) : d226864 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d225806, d226864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22324 q selected
    | true =>
      simp only [d225806, d226864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d225807 q = 0) : d226865 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d225807, d226865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225807, d226865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d225857 q = 0) : d226871 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d225857, d226871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d225857, d226871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d225858 q = 0) : d226872 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d225858, d226872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225858, d226872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225859 q = 0) : d226873 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d225859, d226873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225859, d226873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d225860 q = 0) : d226874 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d225860, d226874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225860, d226874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22334 (p : Pattern) (selected : d225866 p = 0) : d226893 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225861 q = 0) : d226888 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d225861, d226888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22333 q selected
    | true =>
      simp only [d225861, d226888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d225862 q = 0) : d226889 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d225862, d226889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225862, d226889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d225863 q = 0) : d226890 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d225863, d226890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d225863, d226890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d225864 q = 0) : d226891 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d225864, d226891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225864, d226891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d225865 q = 0) : d226892 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d225865, d226892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225865, d226892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d225866 q = 0) : d226893 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d225866, d226893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225866, d226893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22335 (p : Pattern) (selected : d225872 p = 0) : d226899 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225856 q = 0) : d226887 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d225856, d226887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225856, d226887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22332 q selected
  have h2 (q : Pattern) (selected : d225867 q = 0) : d226894 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d225867, d226894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225867, d226894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22334 q selected
  have h3 (q : Pattern) (selected : d225868 q = 0) : d226895 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d225868, d226895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d225868, d226895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d225869 q = 0) : d226896 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d225869, d226896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225869, d226896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225870 q = 0) : d226897 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d225870, d226897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225870, d226897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d225871 q = 0) : d226898 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d225871, d226898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225871, d226898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d225872 q = 0) : d226899 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d225872, d226899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225872, d226899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro22336 (p : Pattern) (selected : d225878 p = 0) : d226905 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225873 q = 0) : d226900 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d225873, d226900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225873, d226900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22335 q selected
  have h2 (q : Pattern) (selected : d225874 q = 0) : d226901 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d225874, d226901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225874, d226901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d225875 q = 0) : d226902 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d225875, d226902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225875, d226902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d225876 q = 0) : d226903 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d225876, d226903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225876, d226903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d225877 q = 0) : d226904 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d225877, d226904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225877, d226904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d225878 q = 0) : d226905 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d225878, d226905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225878, d226905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22337 (p : Pattern) (selected : d225894 p = 0) : d226921 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225880 q = 0) : d226907 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225880, d226907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225880, d226907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro335 q selected
  have h2 (q : Pattern) (selected : d225881 q = 0) : d226908 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225881, d226908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro335 q selected
    | true =>
      simp only [d225881, d226908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d225882 q = 0) : d226909 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225882, d226909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d225882, d226909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d225883 q = 0) : d226910 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225883, d226910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225883, d226910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225884 q = 0) : d226911 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225884, d226911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225884, d226911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6641 q selected
  have h6 (q : Pattern) (selected : d225885 q = 0) : d226912 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225885, d226912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6641 q selected
    | true =>
      simp only [d225885, d226912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d225886 q = 0) : d226913 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225886, d226913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225886, d226913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d225887 q = 0) : d226914 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225887, d226914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d225887, d226914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d225888 q = 0) : d226915 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d225888, d226915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225888, d226915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d225889 q = 0) : d226916 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225889, d226916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225889, d226916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6642 q selected
  have h11 (q : Pattern) (selected : d225890 q = 0) : d226917 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225890, d226917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6642 q selected
    | true =>
      simp only [d225890, d226917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d225891 q = 0) : d226918 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225891, d226918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d225891, d226918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d225892 q = 0) : d226919 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225892, d226919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d225892, d226919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d225779 q = 0) : d226837 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225779, d226837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225779, d226837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6620 q selected
  have h15 (q : Pattern) (selected : d225780 q = 0) : d226838 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225780, d226838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6620 q selected
    | true =>
      simp only [d225780, d226838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d225781 q = 0) : d226839 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225781, d226839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d225781, d226839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d225782 q = 0) : d226840 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225782, d226840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d225782, d226840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d225893 q = 0) : d226920 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d225893, d226920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d225893, d226920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d225894 q = 0) : d226921 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d225894, d226921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d225894, d226921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro22338 (p : Pattern) (selected : d225900 p = 0) : d226927 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225770 q = 0) : d226828 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225770, d226828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225770, d226828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro277 q selected
  have h2 (q : Pattern) (selected : d225771 q = 0) : d226829 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225771, d226829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro277 q selected
    | true =>
      simp only [d225771, d226829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d225772 q = 0) : d226830 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225772, d226830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d225772, d226830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d225773 q = 0) : d226831 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225773, d226831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225773, d226831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225774 q = 0) : d226832 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225774, d226832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225774, d226832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6619 q selected
  have h6 (q : Pattern) (selected : d225775 q = 0) : d226833 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225775, d226833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6619 q selected
    | true =>
      simp only [d225775, d226833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d225776 q = 0) : d226834 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225776, d226834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225776, d226834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d225777 q = 0) : d226835 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225777, d226835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d225777, d226835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d225778 q = 0) : d226836 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d225778, d226836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225778, d226836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d225779 q = 0) : d226837 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225779, d226837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225779, d226837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6620 q selected
  have h11 (q : Pattern) (selected : d225780 q = 0) : d226838 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225780, d226838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6620 q selected
    | true =>
      simp only [d225780, d226838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d225781 q = 0) : d226839 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225781, d226839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d225781, d226839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d225782 q = 0) : d226840 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225782, d226840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d225782, d226840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d225895 q = 0) : d226922 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225895, d226922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225895, d226922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro317 q selected
  have h15 (q : Pattern) (selected : d225896 q = 0) : d226923 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225896, d226923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro317 q selected
    | true =>
      simp only [d225896, d226923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d225897 q = 0) : d226924 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225897, d226924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d225897, d226924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d225898 q = 0) : d226925 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225898, d226925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d225898, d226925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d225899 q = 0) : d226926 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d225899, d226926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d225899, d226926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d225900 q = 0) : d226927 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d225900, d226927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d225900, d226927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro22339 (p : Pattern) (selected : d225904 p = 0) : d226931 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225779 q = 0) : d226837 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225779, d226837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225779, d226837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6620 q selected
  have h2 (q : Pattern) (selected : d225780 q = 0) : d226838 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225780, d226838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6620 q selected
    | true =>
      simp only [d225780, d226838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d225781 q = 0) : d226839 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225781, d226839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d225781, d226839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d225782 q = 0) : d226840 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225782, d226840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225782, d226840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225895 q = 0) : d226922 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225895, d226922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225895, d226922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro317 q selected
  have h6 (q : Pattern) (selected : d225896 q = 0) : d226923 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225896, d226923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro317 q selected
    | true =>
      simp only [d225896, d226923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d225897 q = 0) : d226924 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225897, d226924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225897, d226924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d225898 q = 0) : d226925 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225898, d226925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d225898, d226925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d225899 q = 0) : d226926 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d225899, d226926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225899, d226926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d225903 q = 0) : d226930 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d225903, d226930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d225903, d226930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d225904 q = 0) : d226931 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d225904, d226931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d225904, d226931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22340 (p : Pattern) (selected : d225909 p = 0) : d226936 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225700 q = 0) : d226776 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225700, d226776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225700, d226776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro235 q selected
  have h2 (q : Pattern) (selected : d225701 q = 0) : d226777 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225701, d226777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro235 q selected
    | true =>
      simp only [d225701, d226777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d225702 q = 0) : d226778 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225702, d226778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d225702, d226778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d225703 q = 0) : d226779 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225703, d226779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225703, d226779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225895 q = 0) : d226922 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225895, d226922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225895, d226922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro317 q selected
  have h6 (q : Pattern) (selected : d225896 q = 0) : d226923 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225896, d226923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro317 q selected
    | true =>
      simp only [d225896, d226923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d225897 q = 0) : d226924 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225897, d226924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225897, d226924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d225898 q = 0) : d226925 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225898, d226925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d225898, d226925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d225908 q = 0) : d226935 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d225908, d226935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225908, d226935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d225903 q = 0) : d226930 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d225903, d226930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d225903, d226930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d225909 q = 0) : d226936 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d225909, d226936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d225909, d226936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22341 (p : Pattern) (selected : d225912 p = 0) : d226939 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225895 q = 0) : d226922 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225895, d226922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225895, d226922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro317 q selected
  have h2 (q : Pattern) (selected : d225896 q = 0) : d226923 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225896, d226923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro317 q selected
    | true =>
      simp only [d225896, d226923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d225897 q = 0) : d226924 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225897, d226924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d225897, d226924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d225898 q = 0) : d226925 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225898, d226925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225898, d226925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225903 q = 0) : d226930 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d225903, d226930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225903, d226930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d225912 q = 0) : d226939 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d225912, d226939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225912, d226939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22342 (p : Pattern) (selected : d225917 p = 0) : d226944 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225901 q = 0) : d226928 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d225901, d226928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22337 q selected
    | true =>
      simp only [d225901, d226928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22338 q selected
  have h2 (q : Pattern) (selected : d225902 q = 0) : d226929 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d225902, d226929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225902, d226929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d225905 q = 0) : d226932 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d225905, d226932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22338 q selected
    | true =>
      simp only [d225905, d226932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22339 q selected
  have h4 (q : Pattern) (selected : d225906 q = 0) : d226933 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d225906, d226933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225906, d226933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d225907 q = 0) : d226934 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d225907, d226934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d225907, d226934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d225910 q = 0) : d226937 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d225910, d226937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22338 q selected
    | true =>
      simp only [d225910, d226937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22340 q selected
  have h7 (q : Pattern) (selected : d225911 q = 0) : d226938 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d225911, d226938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225911, d226938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d225913 q = 0) : d226940 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d225913, d226940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22340 q selected
    | true =>
      simp only [d225913, d226940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22341 q selected
  have h9 (q : Pattern) (selected : d225914 q = 0) : d226941 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d225914, d226941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225914, d226941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d225915 q = 0) : d226942 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d225915, d226942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d225915, d226942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d225916 q = 0) : d226943 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d225916, d226943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225916, d226943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d225917 q = 0) : d226944 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d225917, d226944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d225917, d226944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h12 p selected
theorem eqIntro22343 (p : Pattern) (selected : d225922 p = 0) : d226949 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225910 q = 0) : d226937 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d225910, d226937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22338 q selected
    | true =>
      simp only [d225910, d226937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22340 q selected
  have h2 (q : Pattern) (selected : d225911 q = 0) : d226938 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d225911, d226938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225911, d226938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d225913 q = 0) : d226940 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d225913, d226940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22340 q selected
    | true =>
      simp only [d225913, d226940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22341 q selected
  have h4 (q : Pattern) (selected : d225914 q = 0) : d226941 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d225914, d226941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225914, d226941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d225915 q = 0) : d226942 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d225915, d226942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d225915, d226942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d225920 q = 0) : d226947 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d225920, d226947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225920, d226947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d225921 q = 0) : d226948 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d225921, d226948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225921, d226948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d225922 q = 0) : d226949 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d225922, d226949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d225922, d226949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22344 (p : Pattern) (selected : d225928 p = 0) : d226955 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225918 q = 0) : d226945 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d225918, d226945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22342 q selected
    | true =>
      simp only [d225918, d226945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d225919 q = 0) : d226946 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d225919, d226946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225919, d226946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d225923 q = 0) : d226950 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d225923, d226950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22343 q selected
    | true =>
      simp only [d225923, d226950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d225924 q = 0) : d226951 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d225924, d226951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225924, d226951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d225925 q = 0) : d226952 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d225925, d226952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d225925, d226952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d225926 q = 0) : d226953 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d225926, d226953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225926, d226953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d225927 q = 0) : d226954 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d225927, d226954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d225927, d226954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d225928 q = 0) : d226955 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d225928, d226955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d225928, d226955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22345 (p : Pattern) (selected : d225930 p = 0) : d226957 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225913 q = 0) : d226940 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d225913, d226940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22340 q selected
    | true =>
      simp only [d225913, d226940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22341 q selected
  have h2 (q : Pattern) (selected : d225914 q = 0) : d226941 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d225914, d226941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225914, d226941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d225920 q = 0) : d226947 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d225920, d226947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d225920, d226947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d225929 q = 0) : d226956 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d225929, d226956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225929, d226956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225930 q = 0) : d226957 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d225930, d226957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225930, d226957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro22346 (p : Pattern) (selected : d225936 p = 0) : d226963 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225923 q = 0) : d226950 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d225923, d226950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22343 q selected
    | true =>
      simp only [d225923, d226950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d225924 q = 0) : d226951 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d225924, d226951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225924, d226951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d225931 q = 0) : d226958 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d225931, d226958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22345 q selected
    | true =>
      simp only [d225931, d226958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d225932 q = 0) : d226959 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d225932, d226959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225932, d226959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d225933 q = 0) : d226960 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d225933, d226960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d225933, d226960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d225934 q = 0) : d226961 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d225934, d226961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225934, d226961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d225935 q = 0) : d226962 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d225935, d226962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d225935, d226962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d225936 q = 0) : d226963 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d225936, d226963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d225936, d226963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22347 (p : Pattern) (selected : d225956 p = 0) : d226927 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225938 q = 0) : d226828 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225938, d226828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225938, d226828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro341 q selected
  have h2 (q : Pattern) (selected : d225939 q = 0) : d226829 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225939, d226829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro341 q selected
    | true =>
      simp only [d225939, d226829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d225940 q = 0) : d226830 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225940, d226830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d225940, d226830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d225941 q = 0) : d226831 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225941, d226831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225941, d226831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225942 q = 0) : d226832 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225942, d226832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225942, d226832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6654 q selected
  have h6 (q : Pattern) (selected : d225943 q = 0) : d226833 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225943, d226833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6654 q selected
    | true =>
      simp only [d225943, d226833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d225944 q = 0) : d226834 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225944, d226834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225944, d226834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d225945 q = 0) : d226835 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225945, d226835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d225945, d226835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d225946 q = 0) : d226836 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d225946, d226836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225946, d226836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d225947 q = 0) : d226837 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225947, d226837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225947, d226837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6655 q selected
  have h11 (q : Pattern) (selected : d225948 q = 0) : d226838 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225948, d226838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6655 q selected
    | true =>
      simp only [d225948, d226838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d225949 q = 0) : d226839 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225949, d226839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d225949, d226839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d225950 q = 0) : d226840 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225950, d226840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d225950, d226840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d225951 q = 0) : d226922 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225951, d226922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225951, d226922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro342 q selected
  have h15 (q : Pattern) (selected : d225952 q = 0) : d226923 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225952, d226923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro342 q selected
    | true =>
      simp only [d225952, d226923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d225953 q = 0) : d226924 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225953, d226924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d225953, d226924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d225954 q = 0) : d226925 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225954, d226925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d225954, d226925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d225955 q = 0) : d226926 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d225955, d226926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d225955, d226926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d225956 q = 0) : d226927 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d225956, d226927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d225956, d226927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro22348 (p : Pattern) (selected : d225959 p = 0) : d226936 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225813 q = 0) : d226776 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225813, d226776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225813, d226776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro282 q selected
  have h2 (q : Pattern) (selected : d225814 q = 0) : d226777 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225814, d226777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro282 q selected
    | true =>
      simp only [d225814, d226777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d225815 q = 0) : d226778 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225815, d226778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d225815, d226778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d225816 q = 0) : d226779 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225816, d226779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225816, d226779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225951 q = 0) : d226922 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225951, d226922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225951, d226922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro342 q selected
  have h6 (q : Pattern) (selected : d225952 q = 0) : d226923 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225952, d226923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro342 q selected
    | true =>
      simp only [d225952, d226923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d225953 q = 0) : d226924 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225953, d226924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225953, d226924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d225954 q = 0) : d226925 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225954, d226925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d225954, d226925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d225957 q = 0) : d226935 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d225957, d226935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225957, d226935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d225958 q = 0) : d226930 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d225958, d226930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d225958, d226930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d225959 q = 0) : d226936 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d225959, d226936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d225959, d226936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22349 (p : Pattern) (selected : d225962 p = 0) : d226939 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225951 q = 0) : d226922 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225951, d226922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225951, d226922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro342 q selected
  have h2 (q : Pattern) (selected : d225952 q = 0) : d226923 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225952, d226923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro342 q selected
    | true =>
      simp only [d225952, d226923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d225953 q = 0) : d226924 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225953, d226924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d225953, d226924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d225954 q = 0) : d226925 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225954, d226925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225954, d226925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225958 q = 0) : d226930 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d225958, d226930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225958, d226930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d225962 q = 0) : d226939 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d225962, d226939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225962, d226939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22350 (p : Pattern) (selected : d225968 p = 0) : d226949 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225960 q = 0) : d226937 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d225960, d226937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22347 q selected
    | true =>
      simp only [d225960, d226937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22348 q selected
  have h2 (q : Pattern) (selected : d225961 q = 0) : d226938 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d225961, d226938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225961, d226938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d225963 q = 0) : d226940 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d225963, d226940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22348 q selected
    | true =>
      simp only [d225963, d226940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22349 q selected
  have h4 (q : Pattern) (selected : d225964 q = 0) : d226941 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d225964, d226941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225964, d226941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d225965 q = 0) : d226942 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d225965, d226942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d225965, d226942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d225966 q = 0) : d226947 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d225966, d226947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225966, d226947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d225967 q = 0) : d226948 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d225967, d226948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225967, d226948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d225968 q = 0) : d226949 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d225968, d226949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d225968, d226949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22351 (p : Pattern) (selected : d225972 p = 0) : d226957 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225963 q = 0) : d226940 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d225963, d226940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22348 q selected
    | true =>
      simp only [d225963, d226940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22349 q selected
  have h2 (q : Pattern) (selected : d225964 q = 0) : d226941 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d225964, d226941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225964, d226941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d225966 q = 0) : d226947 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d225966, d226947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d225966, d226947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d225971 q = 0) : d226956 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d225971, d226956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225971, d226956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225972 q = 0) : d226957 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d225972, d226957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225972, d226957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro22352 (p : Pattern) (selected : d225978 p = 0) : d226963 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225969 q = 0) : d226950 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d225969, d226950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22350 q selected
    | true =>
      simp only [d225969, d226950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d225970 q = 0) : d226951 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d225970, d226951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225970, d226951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d225973 q = 0) : d226958 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d225973, d226958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22351 q selected
    | true =>
      simp only [d225973, d226958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d225974 q = 0) : d226959 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d225974, d226959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225974, d226959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d225975 q = 0) : d226960 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d225975, d226960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d225975, d226960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d225976 q = 0) : d226961 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d225976, d226961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225976, d226961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d225977 q = 0) : d226962 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d225977, d226962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d225977, d226962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d225978 q = 0) : d226963 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d225978, d226963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d225978, d226963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22353 (p : Pattern) (selected : d225982 p = 0) : d226968 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225973 q = 0) : d226958 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d225973, d226958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22351 q selected
    | true =>
      simp only [d225973, d226958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d225974 q = 0) : d226959 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d225974, d226959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225974, d226959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d225979 q = 0) : d226965 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d225979, d226965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d225979, d226965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d225980 q = 0) : d226966 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d225980, d226966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225980, d226966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225981 q = 0) : d226967 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d225981, d226967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225981, d226967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d225982 q = 0) : d226968 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d225982, d226968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225982, d226968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22354 (p : Pattern) (selected : d225988 p = 0) : d226974 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225923 q = 0) : d226950 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d225923, d226950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22343 q selected
    | true =>
      simp only [d225923, d226950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d225924 q = 0) : d226951 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d225924, d226951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225924, d226951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d225985 q = 0) : d226971 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d225985, d226971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d225985, d226971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d225986 q = 0) : d226972 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d225986, d226972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225986, d226972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225987 q = 0) : d226973 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d225987, d226973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225987, d226973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d225988 q = 0) : d226974 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d225988, d226974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225988, d226974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22355 (p : Pattern) (selected : d225994 p = 0) : d226980 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225937 q = 0) : d226964 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d225937, d226964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22344 q selected
    | true =>
      simp only [d225937, d226964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22346 q selected
  have h2 (q : Pattern) (selected : d225983 q = 0) : d226969 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d225983, d226969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22352 q selected
    | true =>
      simp only [d225983, d226969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22353 q selected
  have h3 (q : Pattern) (selected : d225984 q = 0) : d226970 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d225984, d226970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d225984, d226970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d225989 q = 0) : d226975 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d225989, d226975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22354 q selected
    | true =>
      simp only [d225989, d226975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225990 q = 0) : d226976 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d225990, d226976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225990, d226976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d225991 q = 0) : d226977 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d225991, d226977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225991, d226977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d225992 q = 0) : d226978 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d225992, d226978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225992, d226978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d225993 q = 0) : d226979 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d225993, d226979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225993, d226979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d225994 q = 0) : d226980 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d225994, d226980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225994, d226980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro22356 (p : Pattern) (selected : d225999 p = 0) : d226968 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225931 q = 0) : d226958 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d225931, d226958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22345 q selected
    | true =>
      simp only [d225931, d226958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d225932 q = 0) : d226959 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d225932, d226959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225932, d226959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d225996 q = 0) : d226965 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d225996, d226965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d225996, d226965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d225997 q = 0) : d226966 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d225997, d226966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225997, d226966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225998 q = 0) : d226967 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d225998, d226967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225998, d226967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d225999 q = 0) : d226968 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d225999, d226968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225999, d226968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22357 (p : Pattern) (selected : d226005 p = 0) : d226987 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226000 q = 0) : d226982 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d226000, d226982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22356 q selected
    | true =>
      simp only [d226000, d226982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d226001 q = 0) : d226983 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d226001, d226983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226001, d226983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226002 q = 0) : d226984 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d226002, d226984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226002, d226984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d226003 q = 0) : d226985 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d226003, d226985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226003, d226985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d226004 q = 0) : d226986 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d226004, d226986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226004, d226986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d226005 q = 0) : d226987 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d226005, d226987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226005, d226987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22358 (p : Pattern) (selected : d226011 p = 0) : d226993 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d225995 q = 0) : d226981 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d225995, d226981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225995, d226981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22355 q selected
  have h2 (q : Pattern) (selected : d226006 q = 0) : d226988 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d226006, d226988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226006, d226988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22357 q selected
  have h3 (q : Pattern) (selected : d226007 q = 0) : d226989 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d226007, d226989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226007, d226989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226008 q = 0) : d226990 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d226008, d226990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226008, d226990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226009 q = 0) : d226991 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d226009, d226991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226009, d226991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226010 q = 0) : d226992 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d226010, d226992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226010, d226992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d226011 q = 0) : d226993 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d226011, d226993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226011, d226993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro22359 (p : Pattern) (selected : d226017 p = 0) : d226999 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226012 q = 0) : d226994 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d226012, d226994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226012, d226994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22358 q selected
  have h2 (q : Pattern) (selected : d226013 q = 0) : d226995 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d226013, d226995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226013, d226995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226014 q = 0) : d226996 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d226014, d226996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226014, d226996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226015 q = 0) : d226997 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d226015, d226997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226015, d226997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d226016 q = 0) : d226998 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d226016, d226998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226016, d226998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d226017 q = 0) : d226999 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d226017, d226999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226017, d226999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22360 (p : Pattern) (selected : d226038 p = 0) : d227020 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226020 q = 0) : d227002 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226020, d227002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226020, d227002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro407 q selected
  have h2 (q : Pattern) (selected : d226021 q = 0) : d227003 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226021, d227003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro407 q selected
    | true =>
      simp only [d226021, d227003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226022 q = 0) : d227004 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226022, d227004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226022, d227004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226023 q = 0) : d227005 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226023, d227005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226023, d227005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226024 q = 0) : d227006 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226024, d227006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226024, d227006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6669 q selected
  have h6 (q : Pattern) (selected : d226025 q = 0) : d227007 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226025, d227007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6669 q selected
    | true =>
      simp only [d226025, d227007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d226026 q = 0) : d227008 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226026, d227008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226026, d227008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d226027 q = 0) : d227009 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226027, d227009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d226027, d227009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d226028 q = 0) : d227010 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226028, d227010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226028, d227010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d226029 q = 0) : d227011 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226029, d227011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226029, d227011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6670 q selected
  have h11 (q : Pattern) (selected : d226030 q = 0) : d227012 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226030, d227012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6670 q selected
    | true =>
      simp only [d226030, d227012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d226031 q = 0) : d227013 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226031, d227013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d226031, d227013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d226032 q = 0) : d227014 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226032, d227014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d226032, d227014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d226033 q = 0) : d227015 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226033, d227015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226033, d227015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6672 q selected
  have h15 (q : Pattern) (selected : d226034 q = 0) : d227016 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226034, d227016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6672 q selected
    | true =>
      simp only [d226034, d227016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d226035 q = 0) : d227017 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226035, d227017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d226035, d227017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d226036 q = 0) : d227018 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226036, d227018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d226036, d227018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d226037 q = 0) : d227019 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226037, d227019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d226037, d227019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d226038 q = 0) : d227020 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d226038, d227020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d226038, d227020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro22361 (p : Pattern) (selected : d226053 p = 0) : d227035 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226039 q = 0) : d227021 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226039, d227021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226039, d227021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro386 q selected
  have h2 (q : Pattern) (selected : d226040 q = 0) : d227022 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226040, d227022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro386 q selected
    | true =>
      simp only [d226040, d227022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226041 q = 0) : d227023 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226041, d227023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226041, d227023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226042 q = 0) : d227024 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226042, d227024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226042, d227024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226043 q = 0) : d227025 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226043, d227025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226043, d227025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6674 q selected
  have h6 (q : Pattern) (selected : d226044 q = 0) : d227026 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226044, d227026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6674 q selected
    | true =>
      simp only [d226044, d227026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d226045 q = 0) : d227027 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226045, d227027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226045, d227027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d226046 q = 0) : d227028 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226046, d227028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d226046, d227028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d226047 q = 0) : d227029 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226047, d227029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226047, d227029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d226033 q = 0) : d227015 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226033, d227015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226033, d227015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6672 q selected
  have h11 (q : Pattern) (selected : d226034 q = 0) : d227016 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226034, d227016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6672 q selected
    | true =>
      simp only [d226034, d227016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d226035 q = 0) : d227017 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226035, d227017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d226035, d227017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d226036 q = 0) : d227018 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226036, d227018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d226036, d227018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d226048 q = 0) : d227030 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226048, d227030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226048, d227030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6675 q selected
  have h15 (q : Pattern) (selected : d226049 q = 0) : d227031 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226049, d227031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6675 q selected
    | true =>
      simp only [d226049, d227031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d226050 q = 0) : d227032 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226050, d227032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d226050, d227032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d226051 q = 0) : d227033 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226051, d227033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d226051, d227033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d226052 q = 0) : d227034 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226052, d227034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d226052, d227034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d226053 q = 0) : d227035 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d226053, d227035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d226053, d227035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro22362 (p : Pattern) (selected : d226062 p = 0) : d227044 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226056 q = 0) : d227038 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226056, d227038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226056, d227038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6677 q selected
  have h2 (q : Pattern) (selected : d226057 q = 0) : d227039 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226057, d227039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6677 q selected
    | true =>
      simp only [d226057, d227039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226058 q = 0) : d227040 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226058, d227040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226058, d227040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226059 q = 0) : d227041 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226059, d227041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226059, d227041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226048 q = 0) : d227030 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226048, d227030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226048, d227030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6675 q selected
  have h6 (q : Pattern) (selected : d226049 q = 0) : d227031 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226049, d227031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6675 q selected
    | true =>
      simp only [d226049, d227031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d226050 q = 0) : d227032 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226050, d227032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226050, d227032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d226051 q = 0) : d227033 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226051, d227033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d226051, d227033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d226060 q = 0) : d227042 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226060, d227042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226060, d227042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d226061 q = 0) : d227043 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226061, d227043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d226061, d227043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d226062 q = 0) : d227044 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d226062, d227044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d226062, d227044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22363 (p : Pattern) (selected : d226075 p = 0) : d227057 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226066 q = 0) : d227048 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226066, d227048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226066, d227048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro387 q selected
  have h2 (q : Pattern) (selected : d226067 q = 0) : d227049 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226067, d227049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro387 q selected
    | true =>
      simp only [d226067, d227049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226068 q = 0) : d227050 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226068, d227050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226068, d227050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226069 q = 0) : d227051 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226069, d227051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226069, d227051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226070 q = 0) : d227052 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226070, d227052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226070, d227052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro388 q selected
  have h6 (q : Pattern) (selected : d226071 q = 0) : d227053 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226071, d227053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro388 q selected
    | true =>
      simp only [d226071, d227053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d226072 q = 0) : d227054 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226072, d227054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226072, d227054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d226073 q = 0) : d227055 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226073, d227055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d226073, d227055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d226074 q = 0) : d227056 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226074, d227056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226074, d227056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d226048 q = 0) : d227030 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226048, d227030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226048, d227030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6675 q selected
  have h11 (q : Pattern) (selected : d226049 q = 0) : d227031 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226049, d227031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6675 q selected
    | true =>
      simp only [d226049, d227031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d226050 q = 0) : d227032 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226050, d227032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d226050, d227032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d226051 q = 0) : d227033 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226051, d227033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d226051, d227033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d226061 q = 0) : d227043 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226061, d227043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d226061, d227043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d226075 q = 0) : d227057 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d226075, d227057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d226075, d227057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22364 (p : Pattern) (selected : d226088 p = 0) : d227070 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226078 q = 0) : d227060 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226078, d227060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226078, d227060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2799 q selected
  have h2 (q : Pattern) (selected : d226079 q = 0) : d227061 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226079, d227061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2799 q selected
    | true =>
      simp only [d226079, d227061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226080 q = 0) : d227062 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226080, d227062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226080, d227062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226081 q = 0) : d227063 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226081, d227063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226081, d227063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226082 q = 0) : d227064 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226082, d227064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226082, d227064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226083 q = 0) : d227065 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226083, d227065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226083, d227065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6680 q selected
  have h7 (q : Pattern) (selected : d226084 q = 0) : d227066 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226084, d227066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6680 q selected
    | true =>
      simp only [d226084, d227066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d226085 q = 0) : d227067 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226085, d227067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d226085, d227067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d226086 q = 0) : d227068 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226086, d227068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d226086, d227068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d226087 q = 0) : d227069 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226087, d227069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d226087, d227069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d226088 q = 0) : d227070 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d226088, d227070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226088, d227070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22365 (p : Pattern) (selected : d226093 p = 0) : d227075 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226054 q = 0) : d227036 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226054, d227036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22360 q selected
    | true =>
      simp only [d226054, d227036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22361 q selected
  have h2 (q : Pattern) (selected : d226055 q = 0) : d227037 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226055, d227037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226055, d227037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226063 q = 0) : d227045 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226063, d227045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22361 q selected
    | true =>
      simp only [d226063, d227045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22362 q selected
  have h4 (q : Pattern) (selected : d226064 q = 0) : d227046 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226064, d227046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226064, d227046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d226065 q = 0) : d227047 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d226065, d227047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226065, d227047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d226076 q = 0) : d227058 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226076, d227058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22361 q selected
    | true =>
      simp only [d226076, d227058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22363 q selected
  have h7 (q : Pattern) (selected : d226077 q = 0) : d227059 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226077, d227059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226077, d227059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d226089 q = 0) : d227071 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226089, d227071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22363 q selected
    | true =>
      simp only [d226089, d227071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22364 q selected
  have h9 (q : Pattern) (selected : d226090 q = 0) : d227072 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226090, d227072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226090, d227072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d226091 q = 0) : d227073 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d226091, d227073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d226091, d227073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d226092 q = 0) : d227074 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d226092, d227074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226092, d227074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d226093 q = 0) : d227075 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d226093, d227075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d226093, d227075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h12 p selected
theorem eqIntro22366 (p : Pattern) (selected : d226098 p = 0) : d227080 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226076 q = 0) : d227058 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226076, d227058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22361 q selected
    | true =>
      simp only [d226076, d227058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22363 q selected
  have h2 (q : Pattern) (selected : d226077 q = 0) : d227059 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226077, d227059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226077, d227059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226089 q = 0) : d227071 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226089, d227071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22363 q selected
    | true =>
      simp only [d226089, d227071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22364 q selected
  have h4 (q : Pattern) (selected : d226090 q = 0) : d227072 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226090, d227072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226090, d227072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d226091 q = 0) : d227073 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d226091, d227073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226091, d227073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d226096 q = 0) : d227078 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d226096, d227078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226096, d227078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d226097 q = 0) : d227079 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d226097, d227079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226097, d227079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d226098 q = 0) : d227080 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d226098, d227080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d226098, d227080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22367 (p : Pattern) (selected : d226104 p = 0) : d227086 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226094 q = 0) : d227076 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d226094, d227076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22365 q selected
    | true =>
      simp only [d226094, d227076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d226095 q = 0) : d227077 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d226095, d227077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226095, d227077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226099 q = 0) : d227081 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d226099, d227081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22366 q selected
    | true =>
      simp only [d226099, d227081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d226100 q = 0) : d227082 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d226100, d227082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226100, d227082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d226101 q = 0) : d227083 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d226101, d227083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226101, d227083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d226102 q = 0) : d227084 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d226102, d227084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226102, d227084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d226103 q = 0) : d227085 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d226103, d227085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d226103, d227085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d226104 q = 0) : d227086 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d226104, d227086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d226104, d227086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22368 (p : Pattern) (selected : d226106 p = 0) : d227088 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226070 q = 0) : d227052 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226070, d227052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226070, d227052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro388 q selected
  have h2 (q : Pattern) (selected : d226071 q = 0) : d227053 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226071, d227053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro388 q selected
    | true =>
      simp only [d226071, d227053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226072 q = 0) : d227054 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226072, d227054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226072, d227054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226073 q = 0) : d227055 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226073, d227055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226073, d227055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226105 q = 0) : d227087 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226105, d227087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226105, d227087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226083 q = 0) : d227065 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226083, d227065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226083, d227065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6680 q selected
  have h7 (q : Pattern) (selected : d226084 q = 0) : d227066 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226084, d227066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6680 q selected
    | true =>
      simp only [d226084, d227066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d226085 q = 0) : d227067 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226085, d227067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d226085, d227067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d226086 q = 0) : d227068 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226086, d227068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d226086, d227068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d226087 q = 0) : d227069 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226087, d227069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d226087, d227069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d226106 q = 0) : d227088 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d226106, d227088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226106, d227088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22369 (p : Pattern) (selected : d226111 p = 0) : d227093 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226107 q = 0) : d227089 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226107, d227089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22363 q selected
    | true =>
      simp only [d226107, d227089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22368 q selected
  have h2 (q : Pattern) (selected : d226108 q = 0) : d227090 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226108, d227090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226108, d227090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226109 q = 0) : d227091 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d226109, d227091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226109, d227091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d226110 q = 0) : d227092 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d226110, d227092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226110, d227092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226111 q = 0) : d227093 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d226111, d227093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226111, d227093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro22370 (p : Pattern) (selected : d226117 p = 0) : d227099 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226099 q = 0) : d227081 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d226099, d227081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22366 q selected
    | true =>
      simp only [d226099, d227081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d226100 q = 0) : d227082 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d226100, d227082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226100, d227082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226112 q = 0) : d227094 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d226112, d227094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22369 q selected
    | true =>
      simp only [d226112, d227094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d226113 q = 0) : d227095 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d226113, d227095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226113, d227095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d226114 q = 0) : d227096 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d226114, d227096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226114, d227096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d226115 q = 0) : d227097 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d226115, d227097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226115, d227097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d226116 q = 0) : d227098 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d226116, d227098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d226116, d227098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d226117 q = 0) : d227099 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d226117, d227099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d226117, d227099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22371 (p : Pattern) (selected : d226137 p = 0) : d227035 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226119 q = 0) : d227021 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226119, d227021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226119, d227021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro415 q selected
  have h2 (q : Pattern) (selected : d226120 q = 0) : d227022 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226120, d227022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro415 q selected
    | true =>
      simp only [d226120, d227022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226121 q = 0) : d227023 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226121, d227023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226121, d227023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226122 q = 0) : d227024 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226122, d227024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226122, d227024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226123 q = 0) : d227025 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226123, d227025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226123, d227025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6690 q selected
  have h6 (q : Pattern) (selected : d226124 q = 0) : d227026 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226124, d227026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6690 q selected
    | true =>
      simp only [d226124, d227026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d226125 q = 0) : d227027 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226125, d227027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226125, d227027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d226126 q = 0) : d227028 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226126, d227028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d226126, d227028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d226127 q = 0) : d227029 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226127, d227029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226127, d227029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d226128 q = 0) : d227015 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226128, d227015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226128, d227015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6691 q selected
  have h11 (q : Pattern) (selected : d226129 q = 0) : d227016 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226129, d227016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6691 q selected
    | true =>
      simp only [d226129, d227016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d226130 q = 0) : d227017 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226130, d227017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d226130, d227017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d226131 q = 0) : d227018 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226131, d227018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d226131, d227018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d226132 q = 0) : d227030 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226132, d227030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226132, d227030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6692 q selected
  have h15 (q : Pattern) (selected : d226133 q = 0) : d227031 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226133, d227031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6692 q selected
    | true =>
      simp only [d226133, d227031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d226134 q = 0) : d227032 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226134, d227032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d226134, d227032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d226135 q = 0) : d227033 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226135, d227033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d226135, d227033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d226136 q = 0) : d227034 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226136, d227034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d226136, d227034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d226137 q = 0) : d227035 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d226137, d227035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d226137, d227035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro22372 (p : Pattern) (selected : d226148 p = 0) : d227057 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226138 q = 0) : d227048 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226138, d227048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226138, d227048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro416 q selected
  have h2 (q : Pattern) (selected : d226139 q = 0) : d227049 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226139, d227049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro416 q selected
    | true =>
      simp only [d226139, d227049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226140 q = 0) : d227050 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226140, d227050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226140, d227050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226141 q = 0) : d227051 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226141, d227051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226141, d227051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226142 q = 0) : d227052 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226142, d227052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226142, d227052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro417 q selected
  have h6 (q : Pattern) (selected : d226143 q = 0) : d227053 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226143, d227053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro417 q selected
    | true =>
      simp only [d226143, d227053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d226144 q = 0) : d227054 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226144, d227054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226144, d227054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d226145 q = 0) : d227055 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226145, d227055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d226145, d227055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d226146 q = 0) : d227056 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226146, d227056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226146, d227056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d226132 q = 0) : d227030 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226132, d227030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226132, d227030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6692 q selected
  have h11 (q : Pattern) (selected : d226133 q = 0) : d227031 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226133, d227031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6692 q selected
    | true =>
      simp only [d226133, d227031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d226134 q = 0) : d227032 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226134, d227032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d226134, d227032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d226135 q = 0) : d227033 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226135, d227033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d226135, d227033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d226147 q = 0) : d227043 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226147, d227043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d226147, d227043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d226148 q = 0) : d227057 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d226148, d227057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d226148, d227057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22373 (p : Pattern) (selected : d226161 p = 0) : d227070 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226151 q = 0) : d227060 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226151, d227060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226151, d227060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6695 q selected
  have h2 (q : Pattern) (selected : d226152 q = 0) : d227061 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226152, d227061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6695 q selected
    | true =>
      simp only [d226152, d227061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226153 q = 0) : d227062 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226153, d227062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226153, d227062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226154 q = 0) : d227063 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226154, d227063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226154, d227063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226155 q = 0) : d227064 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226155, d227064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226155, d227064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226156 q = 0) : d227065 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226156, d227065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226156, d227065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6696 q selected
  have h7 (q : Pattern) (selected : d226157 q = 0) : d227066 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226157, d227066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6696 q selected
    | true =>
      simp only [d226157, d227066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d226158 q = 0) : d227067 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226158, d227067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d226158, d227067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d226159 q = 0) : d227068 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226159, d227068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d226159, d227068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d226160 q = 0) : d227069 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226160, d227069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d226160, d227069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d226161 q = 0) : d227070 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d226161, d227070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226161, d227070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22374 (p : Pattern) (selected : d226166 p = 0) : d227088 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226142 q = 0) : d227052 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226142, d227052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226142, d227052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro417 q selected
  have h2 (q : Pattern) (selected : d226143 q = 0) : d227053 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226143, d227053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro417 q selected
    | true =>
      simp only [d226143, d227053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226144 q = 0) : d227054 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226144, d227054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226144, d227054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226145 q = 0) : d227055 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226145, d227055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226145, d227055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226165 q = 0) : d227087 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226165, d227087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226165, d227087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226156 q = 0) : d227065 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226156, d227065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226156, d227065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6696 q selected
  have h7 (q : Pattern) (selected : d226157 q = 0) : d227066 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226157, d227066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6696 q selected
    | true =>
      simp only [d226157, d227066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d226158 q = 0) : d227067 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226158, d227067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d226158, d227067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d226159 q = 0) : d227068 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226159, d227068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d226159, d227068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d226160 q = 0) : d227069 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226160, d227069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d226160, d227069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d226166 q = 0) : d227088 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d226166, d227088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226166, d227088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22375 (p : Pattern) (selected : d226171 p = 0) : d227102 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226149 q = 0) : d227058 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226149, d227058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22371 q selected
    | true =>
      simp only [d226149, d227058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22372 q selected
  have h2 (q : Pattern) (selected : d226150 q = 0) : d227059 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226150, d227059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226150, d227059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226162 q = 0) : d227071 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226162, d227071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22372 q selected
    | true =>
      simp only [d226162, d227071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22373 q selected
  have h4 (q : Pattern) (selected : d226163 q = 0) : d227072 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226163, d227072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226163, d227072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d226164 q = 0) : d227073 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d226164, d227073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226164, d227073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d226167 q = 0) : d227089 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226167, d227089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22372 q selected
    | true =>
      simp only [d226167, d227089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22374 q selected
  have h7 (q : Pattern) (selected : d226168 q = 0) : d227090 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226168, d227090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226168, d227090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d226169 q = 0) : d227091 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d226169, d227091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d226169, d227091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d226170 q = 0) : d227101 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d226170, d227101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226170, d227101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d226171 q = 0) : d227102 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d226171, d227102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d226171, d227102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22376 (p : Pattern) (selected : d226175 p = 0) : d227093 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226167 q = 0) : d227089 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226167, d227089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22372 q selected
    | true =>
      simp only [d226167, d227089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22374 q selected
  have h2 (q : Pattern) (selected : d226168 q = 0) : d227090 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226168, d227090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226168, d227090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226169 q = 0) : d227091 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d226169, d227091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226169, d227091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d226174 q = 0) : d227092 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d226174, d227092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226174, d227092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226175 q = 0) : d227093 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d226175, d227093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226175, d227093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro22377 (p : Pattern) (selected : d226181 p = 0) : d227108 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226172 q = 0) : d227103 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d226172, d227103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22375 q selected
    | true =>
      simp only [d226172, d227103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d226173 q = 0) : d227104 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d226173, d227104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226173, d227104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226176 q = 0) : d227094 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d226176, d227094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22376 q selected
    | true =>
      simp only [d226176, d227094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d226177 q = 0) : d227095 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d226177, d227095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226177, d227095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d226178 q = 0) : d227105 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d226178, d227105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226178, d227105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d226179 q = 0) : d227106 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d226179, d227106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226179, d227106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d226180 q = 0) : d227107 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d226180, d227107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d226180, d227107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d226181 q = 0) : d227108 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d226181, d227108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d226181, d227108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22378 (p : Pattern) (selected : d226185 p = 0) : d227112 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226176 q = 0) : d227094 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d226176, d227094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22376 q selected
    | true =>
      simp only [d226176, d227094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d226177 q = 0) : d227095 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d226177, d227095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226177, d227095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226182 q = 0) : d227109 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d226182, d227109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226182, d227109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d226183 q = 0) : d227110 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d226183, d227110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226183, d227110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226184 q = 0) : d227111 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d226184, d227111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226184, d227111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226185 q = 0) : d227112 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d226185, d227112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226185, d227112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22379 (p : Pattern) (selected : d226188 p = 0) : d227115 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226070 q = 0) : d227052 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226070, d227052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226070, d227052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro388 q selected
  have h2 (q : Pattern) (selected : d226071 q = 0) : d227053 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226071, d227053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro388 q selected
    | true =>
      simp only [d226071, d227053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226072 q = 0) : d227054 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226072, d227054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226072, d227054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226073 q = 0) : d227055 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226073, d227055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226073, d227055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226105 q = 0) : d227087 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226105, d227087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226105, d227087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226188 q = 0) : d227115 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d226188, d227115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226188, d227115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22380 (p : Pattern) (selected : d226193 p = 0) : d227120 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226076 q = 0) : d227058 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226076, d227058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22361 q selected
    | true =>
      simp only [d226076, d227058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22363 q selected
  have h2 (q : Pattern) (selected : d226077 q = 0) : d227059 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226077, d227059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226077, d227059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226089 q = 0) : d227071 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226089, d227071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22363 q selected
    | true =>
      simp only [d226089, d227071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22364 q selected
  have h4 (q : Pattern) (selected : d226090 q = 0) : d227072 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226090, d227072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226090, d227072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d226091 q = 0) : d227073 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d226091, d227073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226091, d227073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d226189 q = 0) : d227116 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226189, d227116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22363 q selected
    | true =>
      simp only [d226189, d227116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22379 q selected
  have h7 (q : Pattern) (selected : d226190 q = 0) : d227117 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226190, d227117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226190, d227117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d226191 q = 0) : d227118 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d226191, d227118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d226191, d227118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d226192 q = 0) : d227119 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d226192, d227119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226192, d227119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d226193 q = 0) : d227120 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d226193, d227120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d226193, d227120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22381 (p : Pattern) (selected : d226199 p = 0) : d227126 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226194 q = 0) : d227121 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d226194, d227121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22380 q selected
    | true =>
      simp only [d226194, d227121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d226195 q = 0) : d227122 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d226195, d227122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226195, d227122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226196 q = 0) : d227123 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d226196, d227123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226196, d227123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d226197 q = 0) : d227124 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d226197, d227124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226197, d227124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226198 q = 0) : d227125 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d226198, d227125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226198, d227125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226199 q = 0) : d227126 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d226199, d227126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226199, d227126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22382 (p : Pattern) (selected : d226205 p = 0) : d227132 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226118 q = 0) : d227100 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d226118, d227100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22367 q selected
    | true =>
      simp only [d226118, d227100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22370 q selected
  have h2 (q : Pattern) (selected : d226186 q = 0) : d227113 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d226186, d227113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22377 q selected
    | true =>
      simp only [d226186, d227113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22378 q selected
  have h3 (q : Pattern) (selected : d226187 q = 0) : d227114 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d226187, d227114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226187, d227114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226200 q = 0) : d227127 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d226200, d227127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22381 q selected
    | true =>
      simp only [d226200, d227127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226201 q = 0) : d227128 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d226201, d227128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226201, d227128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226202 q = 0) : d227129 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d226202, d227129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226202, d227129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d226203 q = 0) : d227130 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d226203, d227130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226203, d227130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d226204 q = 0) : d227131 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d226204, d227131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226204, d227131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d226205 q = 0) : d227132 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d226205, d227132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226205, d227132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro22383 (p : Pattern) (selected : d226210 p = 0) : d227112 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226112 q = 0) : d227094 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d226112, d227094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22369 q selected
    | true =>
      simp only [d226112, d227094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d226113 q = 0) : d227095 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d226113, d227095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226113, d227095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226207 q = 0) : d227109 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d226207, d227109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226207, d227109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d226208 q = 0) : d227110 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d226208, d227110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226208, d227110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226209 q = 0) : d227111 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d226209, d227111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226209, d227111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226210 q = 0) : d227112 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d226210, d227112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226210, d227112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22384 (p : Pattern) (selected : d226216 p = 0) : d227139 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226211 q = 0) : d227134 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d226211, d227134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22383 q selected
    | true =>
      simp only [d226211, d227134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d226212 q = 0) : d227135 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d226212, d227135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226212, d227135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226213 q = 0) : d227136 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d226213, d227136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226213, d227136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d226214 q = 0) : d227137 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d226214, d227137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226214, d227137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d226215 q = 0) : d227138 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d226215, d227138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226215, d227138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d226216 q = 0) : d227139 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d226216, d227139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226216, d227139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22385 (p : Pattern) (selected : d226222 p = 0) : d227145 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226206 q = 0) : d227133 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d226206, d227133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226206, d227133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22382 q selected
  have h2 (q : Pattern) (selected : d226217 q = 0) : d227140 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d226217, d227140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226217, d227140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22384 q selected
  have h3 (q : Pattern) (selected : d226218 q = 0) : d227141 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d226218, d227141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226218, d227141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226219 q = 0) : d227142 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d226219, d227142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226219, d227142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226220 q = 0) : d227143 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d226220, d227143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226220, d227143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226221 q = 0) : d227144 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d226221, d227144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226221, d227144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d226222 q = 0) : d227145 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d226222, d227145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226222, d227145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro22386 (p : Pattern) (selected : d226228 p = 0) : d227151 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226223 q = 0) : d227146 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d226223, d227146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226223, d227146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22385 q selected
  have h2 (q : Pattern) (selected : d226224 q = 0) : d227147 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d226224, d227147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226224, d227147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226225 q = 0) : d227148 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d226225, d227148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226225, d227148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226226 q = 0) : d227149 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d226226, d227149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226226, d227149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d226227 q = 0) : d227150 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d226227, d227150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226227, d227150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d226228 q = 0) : d227151 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d226228, d227151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226228, d227151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22387 (p : Pattern) (selected : d226250 p = 0) : d227173 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226232 q = 0) : d227155 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226232, d227155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226232, d227155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro487 q selected
  have h2 (q : Pattern) (selected : d226233 q = 0) : d227156 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226233, d227156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro487 q selected
    | true =>
      simp only [d226233, d227156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226234 q = 0) : d227157 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226234, d227157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226234, d227157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226235 q = 0) : d227158 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226235, d227158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226235, d227158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226236 q = 0) : d227159 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226236, d227159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226236, d227159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6711 q selected
  have h6 (q : Pattern) (selected : d226237 q = 0) : d227160 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226237, d227160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6711 q selected
    | true =>
      simp only [d226237, d227160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d226238 q = 0) : d227161 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226238, d227161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226238, d227161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d226239 q = 0) : d227162 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226239, d227162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d226239, d227162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d226240 q = 0) : d227163 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226240, d227163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226240, d227163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d226241 q = 0) : d227164 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226241, d227164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226241, d227164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6712 q selected
  have h11 (q : Pattern) (selected : d226242 q = 0) : d227165 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226242, d227165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6712 q selected
    | true =>
      simp only [d226242, d227165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d226243 q = 0) : d227166 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226243, d227166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d226243, d227166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d226244 q = 0) : d227167 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226244, d227167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d226244, d227167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d226245 q = 0) : d227168 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226245, d227168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226245, d227168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6714 q selected
  have h15 (q : Pattern) (selected : d226246 q = 0) : d227169 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226246, d227169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6714 q selected
    | true =>
      simp only [d226246, d227169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d226247 q = 0) : d227170 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226247, d227170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d226247, d227170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d226248 q = 0) : d227171 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226248, d227171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d226248, d227171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d226249 q = 0) : d227172 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226249, d227172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d226249, d227172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d226250 q = 0) : d227173 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d226250, d227173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d226250, d227173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro22388 (p : Pattern) (selected : d226265 p = 0) : d227188 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226251 q = 0) : d227174 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226251, d227174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226251, d227174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro466 q selected
  have h2 (q : Pattern) (selected : d226252 q = 0) : d227175 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226252, d227175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro466 q selected
    | true =>
      simp only [d226252, d227175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226253 q = 0) : d227176 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226253, d227176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226253, d227176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226254 q = 0) : d227177 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226254, d227177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226254, d227177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226255 q = 0) : d227178 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226255, d227178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226255, d227178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6716 q selected
  have h6 (q : Pattern) (selected : d226256 q = 0) : d227179 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226256, d227179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6716 q selected
    | true =>
      simp only [d226256, d227179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d226257 q = 0) : d227180 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226257, d227180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226257, d227180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d226258 q = 0) : d227181 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226258, d227181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d226258, d227181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d226259 q = 0) : d227182 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226259, d227182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226259, d227182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d226245 q = 0) : d227168 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226245, d227168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226245, d227168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6714 q selected
  have h11 (q : Pattern) (selected : d226246 q = 0) : d227169 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226246, d227169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6714 q selected
    | true =>
      simp only [d226246, d227169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d226247 q = 0) : d227170 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226247, d227170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d226247, d227170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d226248 q = 0) : d227171 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226248, d227171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d226248, d227171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d226260 q = 0) : d227183 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226260, d227183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226260, d227183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6717 q selected
  have h15 (q : Pattern) (selected : d226261 q = 0) : d227184 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226261, d227184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6717 q selected
    | true =>
      simp only [d226261, d227184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d226262 q = 0) : d227185 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226262, d227185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d226262, d227185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d226263 q = 0) : d227186 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226263, d227186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d226263, d227186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d226264 q = 0) : d227187 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226264, d227187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d226264, d227187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d226265 q = 0) : d227188 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d226265, d227188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d226265, d227188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro22389 (p : Pattern) (selected : d226274 p = 0) : d227197 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226268 q = 0) : d227191 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226268, d227191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226268, d227191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6719 q selected
  have h2 (q : Pattern) (selected : d226269 q = 0) : d227192 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226269, d227192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6719 q selected
    | true =>
      simp only [d226269, d227192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226270 q = 0) : d227193 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226270, d227193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226270, d227193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226271 q = 0) : d227194 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226271, d227194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226271, d227194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226260 q = 0) : d227183 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226260, d227183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226260, d227183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6717 q selected
  have h6 (q : Pattern) (selected : d226261 q = 0) : d227184 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226261, d227184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6717 q selected
    | true =>
      simp only [d226261, d227184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d226262 q = 0) : d227185 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226262, d227185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226262, d227185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d226263 q = 0) : d227186 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226263, d227186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d226263, d227186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d226272 q = 0) : d227195 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226272, d227195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226272, d227195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d226273 q = 0) : d227196 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226273, d227196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d226273, d227196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d226274 q = 0) : d227197 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d226274, d227197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d226274, d227197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22390 (p : Pattern) (selected : d226287 p = 0) : d227210 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226278 q = 0) : d227201 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226278, d227201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226278, d227201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro469 q selected
  have h2 (q : Pattern) (selected : d226279 q = 0) : d227202 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226279, d227202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro469 q selected
    | true =>
      simp only [d226279, d227202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226280 q = 0) : d227203 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226280, d227203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226280, d227203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226281 q = 0) : d227204 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226281, d227204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226281, d227204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226282 q = 0) : d227205 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226282, d227205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226282, d227205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6721 q selected
  have h6 (q : Pattern) (selected : d226283 q = 0) : d227206 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226283, d227206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6721 q selected
    | true =>
      simp only [d226283, d227206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d226284 q = 0) : d227207 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226284, d227207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226284, d227207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d226285 q = 0) : d227208 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226285, d227208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d226285, d227208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d226286 q = 0) : d227209 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226286, d227209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226286, d227209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d226260 q = 0) : d227183 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226260, d227183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226260, d227183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6717 q selected
  have h11 (q : Pattern) (selected : d226261 q = 0) : d227184 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226261, d227184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6717 q selected
    | true =>
      simp only [d226261, d227184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d226262 q = 0) : d227185 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226262, d227185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d226262, d227185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d226263 q = 0) : d227186 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226263, d227186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d226263, d227186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d226273 q = 0) : d227196 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226273, d227196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d226273, d227196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d226287 q = 0) : d227210 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d226287, d227210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d226287, d227210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22391 (p : Pattern) (selected : d226300 p = 0) : d227223 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226290 q = 0) : d227213 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226290, d227213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226290, d227213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2814 q selected
  have h2 (q : Pattern) (selected : d226291 q = 0) : d227214 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226291, d227214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2814 q selected
    | true =>
      simp only [d226291, d227214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226292 q = 0) : d227215 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226292, d227215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226292, d227215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226293 q = 0) : d227216 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226293, d227216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226293, d227216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226294 q = 0) : d227217 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226294, d227217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226294, d227217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226295 q = 0) : d227218 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226295, d227218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226295, d227218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6723 q selected
  have h7 (q : Pattern) (selected : d226296 q = 0) : d227219 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226296, d227219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6723 q selected
    | true =>
      simp only [d226296, d227219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d226297 q = 0) : d227220 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226297, d227220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d226297, d227220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d226298 q = 0) : d227221 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226298, d227221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d226298, d227221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d226299 q = 0) : d227222 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226299, d227222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d226299, d227222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d226300 q = 0) : d227223 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d226300, d227223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226300, d227223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22392 (p : Pattern) (selected : d226305 p = 0) : d227228 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226266 q = 0) : d227189 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226266, d227189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22387 q selected
    | true =>
      simp only [d226266, d227189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22388 q selected
  have h2 (q : Pattern) (selected : d226267 q = 0) : d227190 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226267, d227190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226267, d227190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226275 q = 0) : d227198 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226275, d227198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22388 q selected
    | true =>
      simp only [d226275, d227198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22389 q selected
  have h4 (q : Pattern) (selected : d226276 q = 0) : d227199 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226276, d227199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226276, d227199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d226277 q = 0) : d227200 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d226277, d227200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226277, d227200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d226288 q = 0) : d227211 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226288, d227211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22388 q selected
    | true =>
      simp only [d226288, d227211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22390 q selected
  have h7 (q : Pattern) (selected : d226289 q = 0) : d227212 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226289, d227212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226289, d227212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d226301 q = 0) : d227224 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226301, d227224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22390 q selected
    | true =>
      simp only [d226301, d227224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22391 q selected
  have h9 (q : Pattern) (selected : d226302 q = 0) : d227225 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226302, d227225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226302, d227225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d226303 q = 0) : d227226 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d226303, d227226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d226303, d227226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d226304 q = 0) : d227227 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d226304, d227227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226304, d227227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d226305 q = 0) : d227228 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d226305, d227228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d226305, d227228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h12 p selected
theorem eqIntro22393 (p : Pattern) (selected : d226310 p = 0) : d227233 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226288 q = 0) : d227211 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226288, d227211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22388 q selected
    | true =>
      simp only [d226288, d227211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22390 q selected
  have h2 (q : Pattern) (selected : d226289 q = 0) : d227212 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226289, d227212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226289, d227212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226301 q = 0) : d227224 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226301, d227224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22390 q selected
    | true =>
      simp only [d226301, d227224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22391 q selected
  have h4 (q : Pattern) (selected : d226302 q = 0) : d227225 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226302, d227225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226302, d227225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d226303 q = 0) : d227226 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d226303, d227226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226303, d227226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d226308 q = 0) : d227231 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d226308, d227231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226308, d227231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d226309 q = 0) : d227232 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d226309, d227232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226309, d227232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d226310 q = 0) : d227233 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d226310, d227233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d226310, d227233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22394 (p : Pattern) (selected : d226316 p = 0) : d227239 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226306 q = 0) : d227229 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d226306, d227229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22392 q selected
    | true =>
      simp only [d226306, d227229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d226307 q = 0) : d227230 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d226307, d227230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226307, d227230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226311 q = 0) : d227234 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d226311, d227234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22393 q selected
    | true =>
      simp only [d226311, d227234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d226312 q = 0) : d227235 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d226312, d227235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226312, d227235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d226313 q = 0) : d227236 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d226313, d227236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226313, d227236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d226314 q = 0) : d227237 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d226314, d227237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226314, d227237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d226315 q = 0) : d227238 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d226315, d227238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d226315, d227238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d226316 q = 0) : d227239 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d226316, d227239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d226316, d227239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22395 (p : Pattern) (selected : d226322 p = 0) : d227245 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226317 q = 0) : d227240 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226317, d227240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226317, d227240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro470 q selected
  have h2 (q : Pattern) (selected : d226318 q = 0) : d227241 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226318, d227241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro470 q selected
    | true =>
      simp only [d226318, d227241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226319 q = 0) : d227242 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226319, d227242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226319, d227242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226320 q = 0) : d227243 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226320, d227243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226320, d227243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226321 q = 0) : d227244 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226321, d227244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226321, d227244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226295 q = 0) : d227218 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226295, d227218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226295, d227218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6723 q selected
  have h7 (q : Pattern) (selected : d226296 q = 0) : d227219 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226296, d227219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6723 q selected
    | true =>
      simp only [d226296, d227219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d226297 q = 0) : d227220 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226297, d227220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d226297, d227220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d226298 q = 0) : d227221 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226298, d227221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d226298, d227221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d226299 q = 0) : d227222 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226299, d227222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d226299, d227222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d226322 q = 0) : d227245 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d226322, d227245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226322, d227245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22396 (p : Pattern) (selected : d226327 p = 0) : d227250 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226323 q = 0) : d227246 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226323, d227246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22390 q selected
    | true =>
      simp only [d226323, d227246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22395 q selected
  have h2 (q : Pattern) (selected : d226324 q = 0) : d227247 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226324, d227247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226324, d227247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226325 q = 0) : d227248 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d226325, d227248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226325, d227248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d226326 q = 0) : d227249 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d226326, d227249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226326, d227249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226327 q = 0) : d227250 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d226327, d227250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226327, d227250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro22397 (p : Pattern) (selected : d226333 p = 0) : d227256 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226311 q = 0) : d227234 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d226311, d227234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22393 q selected
    | true =>
      simp only [d226311, d227234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d226312 q = 0) : d227235 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d226312, d227235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226312, d227235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226328 q = 0) : d227251 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d226328, d227251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22396 q selected
    | true =>
      simp only [d226328, d227251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d226329 q = 0) : d227252 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d226329, d227252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226329, d227252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d226330 q = 0) : d227253 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d226330, d227253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226330, d227253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d226331 q = 0) : d227254 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d226331, d227254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226331, d227254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d226332 q = 0) : d227255 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d226332, d227255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d226332, d227255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d226333 q = 0) : d227256 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d226333, d227256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d226333, d227256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22398 (p : Pattern) (selected : d226353 p = 0) : d227188 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226335 q = 0) : d227174 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226335, d227174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226335, d227174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro499 q selected
  have h2 (q : Pattern) (selected : d226336 q = 0) : d227175 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226336, d227175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro499 q selected
    | true =>
      simp only [d226336, d227175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226337 q = 0) : d227176 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226337, d227176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226337, d227176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226338 q = 0) : d227177 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226338, d227177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226338, d227177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226339 q = 0) : d227178 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226339, d227178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226339, d227178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6733 q selected
  have h6 (q : Pattern) (selected : d226340 q = 0) : d227179 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226340, d227179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6733 q selected
    | true =>
      simp only [d226340, d227179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d226341 q = 0) : d227180 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226341, d227180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226341, d227180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d226342 q = 0) : d227181 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226342, d227181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d226342, d227181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d226343 q = 0) : d227182 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226343, d227182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226343, d227182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d226344 q = 0) : d227168 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226344, d227168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226344, d227168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6734 q selected
  have h11 (q : Pattern) (selected : d226345 q = 0) : d227169 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226345, d227169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6734 q selected
    | true =>
      simp only [d226345, d227169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d226346 q = 0) : d227170 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226346, d227170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d226346, d227170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d226347 q = 0) : d227171 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226347, d227171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d226347, d227171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d226348 q = 0) : d227183 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226348, d227183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226348, d227183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6735 q selected
  have h15 (q : Pattern) (selected : d226349 q = 0) : d227184 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226349, d227184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6735 q selected
    | true =>
      simp only [d226349, d227184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d226350 q = 0) : d227185 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226350, d227185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d226350, d227185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d226351 q = 0) : d227186 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226351, d227186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d226351, d227186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d226352 q = 0) : d227187 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226352, d227187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d226352, d227187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d226353 q = 0) : d227188 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d226353, d227188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d226353, d227188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro22399 (p : Pattern) (selected : d226364 p = 0) : d227210 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226354 q = 0) : d227201 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226354, d227201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226354, d227201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro502 q selected
  have h2 (q : Pattern) (selected : d226355 q = 0) : d227202 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226355, d227202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro502 q selected
    | true =>
      simp only [d226355, d227202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226356 q = 0) : d227203 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226356, d227203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226356, d227203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226357 q = 0) : d227204 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226357, d227204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226357, d227204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226358 q = 0) : d227205 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226358, d227205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226358, d227205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6737 q selected
  have h6 (q : Pattern) (selected : d226359 q = 0) : d227206 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226359, d227206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6737 q selected
    | true =>
      simp only [d226359, d227206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d226360 q = 0) : d227207 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226360, d227207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226360, d227207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d226361 q = 0) : d227208 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226361, d227208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d226361, d227208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d226362 q = 0) : d227209 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226362, d227209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226362, d227209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d226348 q = 0) : d227183 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226348, d227183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226348, d227183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6735 q selected
  have h11 (q : Pattern) (selected : d226349 q = 0) : d227184 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226349, d227184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6735 q selected
    | true =>
      simp only [d226349, d227184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d226350 q = 0) : d227185 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226350, d227185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d226350, d227185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d226351 q = 0) : d227186 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226351, d227186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d226351, d227186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d226363 q = 0) : d227196 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226363, d227196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d226363, d227196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d226364 q = 0) : d227210 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d226364, d227210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d226364, d227210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22400 (p : Pattern) (selected : d226377 p = 0) : d227223 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226367 q = 0) : d227213 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226367, d227213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226367, d227213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6739 q selected
  have h2 (q : Pattern) (selected : d226368 q = 0) : d227214 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226368, d227214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6739 q selected
    | true =>
      simp only [d226368, d227214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226369 q = 0) : d227215 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226369, d227215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226369, d227215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226370 q = 0) : d227216 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226370, d227216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226370, d227216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226371 q = 0) : d227217 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226371, d227217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226371, d227217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226372 q = 0) : d227218 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226372, d227218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226372, d227218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6740 q selected
  have h7 (q : Pattern) (selected : d226373 q = 0) : d227219 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226373, d227219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6740 q selected
    | true =>
      simp only [d226373, d227219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d226374 q = 0) : d227220 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226374, d227220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d226374, d227220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d226375 q = 0) : d227221 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226375, d227221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d226375, d227221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d226376 q = 0) : d227222 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226376, d227222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d226376, d227222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d226377 q = 0) : d227223 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d226377, d227223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226377, d227223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22401 (p : Pattern) (selected : d226386 p = 0) : d227245 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226381 q = 0) : d227240 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226381, d227240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226381, d227240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro503 q selected
  have h2 (q : Pattern) (selected : d226382 q = 0) : d227241 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226382, d227241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro503 q selected
    | true =>
      simp only [d226382, d227241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226383 q = 0) : d227242 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226383, d227242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226383, d227242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226384 q = 0) : d227243 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226384, d227243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226384, d227243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226385 q = 0) : d227244 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226385, d227244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226385, d227244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226372 q = 0) : d227218 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226372, d227218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226372, d227218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6740 q selected
  have h7 (q : Pattern) (selected : d226373 q = 0) : d227219 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226373, d227219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6740 q selected
    | true =>
      simp only [d226373, d227219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d226374 q = 0) : d227220 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226374, d227220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d226374, d227220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d226375 q = 0) : d227221 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226375, d227221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d226375, d227221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d226376 q = 0) : d227222 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226376, d227222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d226376, d227222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d226386 q = 0) : d227245 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d226386, d227245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226386, d227245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22402 (p : Pattern) (selected : d226391 p = 0) : d227259 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226365 q = 0) : d227211 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226365, d227211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22398 q selected
    | true =>
      simp only [d226365, d227211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22399 q selected
  have h2 (q : Pattern) (selected : d226366 q = 0) : d227212 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226366, d227212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226366, d227212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226378 q = 0) : d227224 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226378, d227224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22399 q selected
    | true =>
      simp only [d226378, d227224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22400 q selected
  have h4 (q : Pattern) (selected : d226379 q = 0) : d227225 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226379, d227225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226379, d227225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d226380 q = 0) : d227226 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d226380, d227226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226380, d227226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d226387 q = 0) : d227246 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226387, d227246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22399 q selected
    | true =>
      simp only [d226387, d227246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22401 q selected
  have h7 (q : Pattern) (selected : d226388 q = 0) : d227247 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226388, d227247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226388, d227247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d226389 q = 0) : d227248 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d226389, d227248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d226389, d227248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d226390 q = 0) : d227258 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d226390, d227258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226390, d227258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d226391 q = 0) : d227259 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d226391, d227259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d226391, d227259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22403 (p : Pattern) (selected : d226395 p = 0) : d227250 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226387 q = 0) : d227246 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226387, d227246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22399 q selected
    | true =>
      simp only [d226387, d227246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22401 q selected
  have h2 (q : Pattern) (selected : d226388 q = 0) : d227247 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226388, d227247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226388, d227247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226389 q = 0) : d227248 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d226389, d227248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226389, d227248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d226394 q = 0) : d227249 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d226394, d227249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226394, d227249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226395 q = 0) : d227250 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d226395, d227250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226395, d227250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro22404 (p : Pattern) (selected : d226401 p = 0) : d227265 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226392 q = 0) : d227260 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d226392, d227260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22402 q selected
    | true =>
      simp only [d226392, d227260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d226393 q = 0) : d227261 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d226393, d227261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226393, d227261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226396 q = 0) : d227251 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d226396, d227251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22403 q selected
    | true =>
      simp only [d226396, d227251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d226397 q = 0) : d227252 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d226397, d227252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226397, d227252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d226398 q = 0) : d227262 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d226398, d227262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226398, d227262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d226399 q = 0) : d227263 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d226399, d227263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226399, d227263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d226400 q = 0) : d227264 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d226400, d227264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d226400, d227264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d226401 q = 0) : d227265 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d226401, d227265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d226401, d227265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22405 (p : Pattern) (selected : d226405 p = 0) : d227269 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226396 q = 0) : d227251 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d226396, d227251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22403 q selected
    | true =>
      simp only [d226396, d227251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d226397 q = 0) : d227252 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d226397, d227252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226397, d227252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226402 q = 0) : d227266 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d226402, d227266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226402, d227266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d226403 q = 0) : d227267 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d226403, d227267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226403, d227267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226404 q = 0) : d227268 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d226404, d227268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226404, d227268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226405 q = 0) : d227269 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d226405, d227269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226405, d227269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22406 (p : Pattern) (selected : d226408 p = 0) : d227272 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226317 q = 0) : d227240 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226317, d227240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226317, d227240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro470 q selected
  have h2 (q : Pattern) (selected : d226318 q = 0) : d227241 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226318, d227241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro470 q selected
    | true =>
      simp only [d226318, d227241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226319 q = 0) : d227242 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226319, d227242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226319, d227242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226320 q = 0) : d227243 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226320, d227243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226320, d227243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226321 q = 0) : d227244 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226321, d227244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226321, d227244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226408 q = 0) : d227272 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d226408, d227272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226408, d227272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22407 (p : Pattern) (selected : d226413 p = 0) : d227277 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226288 q = 0) : d227211 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226288, d227211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22388 q selected
    | true =>
      simp only [d226288, d227211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22390 q selected
  have h2 (q : Pattern) (selected : d226289 q = 0) : d227212 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226289, d227212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226289, d227212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226301 q = 0) : d227224 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226301, d227224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22390 q selected
    | true =>
      simp only [d226301, d227224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22391 q selected
  have h4 (q : Pattern) (selected : d226302 q = 0) : d227225 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226302, d227225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226302, d227225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d226303 q = 0) : d227226 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d226303, d227226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226303, d227226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d226409 q = 0) : d227273 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226409, d227273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22390 q selected
    | true =>
      simp only [d226409, d227273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22406 q selected
  have h7 (q : Pattern) (selected : d226410 q = 0) : d227274 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226410, d227274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226410, d227274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d226411 q = 0) : d227275 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d226411, d227275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d226411, d227275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d226412 q = 0) : d227276 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d226412, d227276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226412, d227276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d226413 q = 0) : d227277 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d226413, d227277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d226413, d227277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22408 (p : Pattern) (selected : d226419 p = 0) : d227283 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226414 q = 0) : d227278 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d226414, d227278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22407 q selected
    | true =>
      simp only [d226414, d227278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d226415 q = 0) : d227279 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d226415, d227279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226415, d227279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226416 q = 0) : d227280 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d226416, d227280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226416, d227280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d226417 q = 0) : d227281 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d226417, d227281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226417, d227281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226418 q = 0) : d227282 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d226418, d227282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226418, d227282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226419 q = 0) : d227283 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d226419, d227283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226419, d227283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22409 (p : Pattern) (selected : d226425 p = 0) : d227289 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226334 q = 0) : d227257 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d226334, d227257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22394 q selected
    | true =>
      simp only [d226334, d227257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22397 q selected
  have h2 (q : Pattern) (selected : d226406 q = 0) : d227270 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d226406, d227270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22404 q selected
    | true =>
      simp only [d226406, d227270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22405 q selected
  have h3 (q : Pattern) (selected : d226407 q = 0) : d227271 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d226407, d227271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226407, d227271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226420 q = 0) : d227284 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d226420, d227284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22408 q selected
    | true =>
      simp only [d226420, d227284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226421 q = 0) : d227285 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d226421, d227285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226421, d227285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226422 q = 0) : d227286 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d226422, d227286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226422, d227286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d226423 q = 0) : d227287 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d226423, d227287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226423, d227287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d226424 q = 0) : d227288 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d226424, d227288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226424, d227288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d226425 q = 0) : d227289 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d226425, d227289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226425, d227289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro22410 (p : Pattern) (selected : d226430 p = 0) : d227269 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226328 q = 0) : d227251 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d226328, d227251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22396 q selected
    | true =>
      simp only [d226328, d227251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d226329 q = 0) : d227252 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d226329, d227252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226329, d227252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226427 q = 0) : d227266 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d226427, d227266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226427, d227266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d226428 q = 0) : d227267 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d226428, d227267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226428, d227267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226429 q = 0) : d227268 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d226429, d227268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226429, d227268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226430 q = 0) : d227269 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d226430, d227269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226430, d227269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22411 (p : Pattern) (selected : d226436 p = 0) : d227296 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226431 q = 0) : d227291 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d226431, d227291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22410 q selected
    | true =>
      simp only [d226431, d227291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d226432 q = 0) : d227292 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d226432, d227292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226432, d227292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226433 q = 0) : d227293 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d226433, d227293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226433, d227293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d226434 q = 0) : d227294 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d226434, d227294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226434, d227294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d226435 q = 0) : d227295 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d226435, d227295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226435, d227295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d226436 q = 0) : d227296 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d226436, d227296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226436, d227296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22412 (p : Pattern) (selected : d226442 p = 0) : d227302 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226426 q = 0) : d227290 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d226426, d227290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226426, d227290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22409 q selected
  have h2 (q : Pattern) (selected : d226437 q = 0) : d227297 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d226437, d227297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226437, d227297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22411 q selected
  have h3 (q : Pattern) (selected : d226438 q = 0) : d227298 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d226438, d227298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226438, d227298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226439 q = 0) : d227299 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d226439, d227299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226439, d227299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226440 q = 0) : d227300 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d226440, d227300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226440, d227300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226441 q = 0) : d227301 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d226441, d227301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226441, d227301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d226442 q = 0) : d227302 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d226442, d227302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226442, d227302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro22413 (p : Pattern) (selected : d226448 p = 0) : d227308 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226443 q = 0) : d227303 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d226443, d227303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226443, d227303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22412 q selected
  have h2 (q : Pattern) (selected : d226444 q = 0) : d227304 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d226444, d227304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226444, d227304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226445 q = 0) : d227305 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d226445, d227305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226445, d227305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226446 q = 0) : d227306 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d226446, d227306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226446, d227306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d226447 q = 0) : d227307 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d226447, d227307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226447, d227307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d226448 q = 0) : d227308 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d226448, d227308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226448, d227308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22414 (p : Pattern) (selected : d226467 p = 0) : d227327 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226453 q = 0) : d227313 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226453, d227313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226453, d227313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro576 q selected
  have h2 (q : Pattern) (selected : d226454 q = 0) : d227314 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226454, d227314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro576 q selected
    | true =>
      simp only [d226454, d227314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226455 q = 0) : d227315 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226455, d227315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226455, d227315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226456 q = 0) : d227316 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226456, d227316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226456, d227316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226457 q = 0) : d227317 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226457, d227317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226457, d227317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6755 q selected
  have h6 (q : Pattern) (selected : d226458 q = 0) : d227318 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226458, d227318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6755 q selected
    | true =>
      simp only [d226458, d227318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d226459 q = 0) : d227319 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226459, d227319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226459, d227319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d226460 q = 0) : d227320 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226460, d227320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d226460, d227320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d226461 q = 0) : d227321 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226461, d227321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226461, d227321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d226462 q = 0) : d227322 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226462, d227322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226462, d227322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6756 q selected
  have h11 (q : Pattern) (selected : d226463 q = 0) : d227323 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226463, d227323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6756 q selected
    | true =>
      simp only [d226463, d227323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d226464 q = 0) : d227324 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226464, d227324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d226464, d227324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d226465 q = 0) : d227325 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226465, d227325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d226465, d227325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d226466 q = 0) : d227326 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226466, d227326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226466, d227326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d226467 q = 0) : d227327 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d226467, d227327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d226467, d227327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22415 (p : Pattern) (selected : d226482 p = 0) : d227342 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226468 q = 0) : d227328 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226468, d227328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226468, d227328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro553 q selected
  have h2 (q : Pattern) (selected : d226469 q = 0) : d227329 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226469, d227329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro553 q selected
    | true =>
      simp only [d226469, d227329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226470 q = 0) : d227330 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226470, d227330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226470, d227330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226471 q = 0) : d227331 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226471, d227331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226471, d227331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226472 q = 0) : d227332 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226472, d227332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226472, d227332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6758 q selected
  have h6 (q : Pattern) (selected : d226473 q = 0) : d227333 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226473, d227333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6758 q selected
    | true =>
      simp only [d226473, d227333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d226474 q = 0) : d227334 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226474, d227334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226474, d227334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d226475 q = 0) : d227335 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226475, d227335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d226475, d227335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d226476 q = 0) : d227336 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226476, d227336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226476, d227336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d226462 q = 0) : d227322 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226462, d227322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226462, d227322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6756 q selected
  have h11 (q : Pattern) (selected : d226463 q = 0) : d227323 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226463, d227323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6756 q selected
    | true =>
      simp only [d226463, d227323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d226464 q = 0) : d227324 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226464, d227324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d226464, d227324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d226465 q = 0) : d227325 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226465, d227325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d226465, d227325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d226477 q = 0) : d227337 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226477, d227337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226477, d227337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6759 q selected
  have h15 (q : Pattern) (selected : d226478 q = 0) : d227338 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226478, d227338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6759 q selected
    | true =>
      simp only [d226478, d227338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d226479 q = 0) : d227339 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226479, d227339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d226479, d227339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d226480 q = 0) : d227340 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226480, d227340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d226480, d227340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d226481 q = 0) : d227341 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226481, d227341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d226481, d227341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d226482 q = 0) : d227342 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d226482, d227342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d226482, d227342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro22416 (p : Pattern) (selected : d226486 p = 0) : d227346 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226462 q = 0) : d227322 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226462, d227322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226462, d227322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6756 q selected
  have h2 (q : Pattern) (selected : d226463 q = 0) : d227323 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226463, d227323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6756 q selected
    | true =>
      simp only [d226463, d227323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226464 q = 0) : d227324 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226464, d227324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226464, d227324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226465 q = 0) : d227325 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226465, d227325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226465, d227325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226477 q = 0) : d227337 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226477, d227337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226477, d227337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6759 q selected
  have h6 (q : Pattern) (selected : d226478 q = 0) : d227338 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226478, d227338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6759 q selected
    | true =>
      simp only [d226478, d227338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d226479 q = 0) : d227339 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226479, d227339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226479, d227339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d226480 q = 0) : d227340 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226480, d227340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d226480, d227340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d226481 q = 0) : d227341 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226481, d227341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226481, d227341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d226485 q = 0) : d227345 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226485, d227345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d226485, d227345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d226486 q = 0) : d227346 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d226486, d227346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d226486, d227346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22417 (p : Pattern) (selected : d226499 p = 0) : d227359 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226490 q = 0) : d227350 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226490, d227350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226490, d227350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro558 q selected
  have h2 (q : Pattern) (selected : d226491 q = 0) : d227351 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226491, d227351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro558 q selected
    | true =>
      simp only [d226491, d227351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226492 q = 0) : d227352 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226492, d227352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226492, d227352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226493 q = 0) : d227353 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226493, d227353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226493, d227353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226494 q = 0) : d227354 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226494, d227354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226494, d227354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6762 q selected
  have h6 (q : Pattern) (selected : d226495 q = 0) : d227355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226495, d227355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6762 q selected
    | true =>
      simp only [d226495, d227355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d226496 q = 0) : d227356 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226496, d227356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226496, d227356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d226497 q = 0) : d227357 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226497, d227357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d226497, d227357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d226498 q = 0) : d227358 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226498, d227358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226498, d227358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d226477 q = 0) : d227337 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226477, d227337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226477, d227337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6759 q selected
  have h11 (q : Pattern) (selected : d226478 q = 0) : d227338 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226478, d227338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6759 q selected
    | true =>
      simp only [d226478, d227338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d226479 q = 0) : d227339 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226479, d227339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d226479, d227339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d226480 q = 0) : d227340 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226480, d227340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d226480, d227340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d226485 q = 0) : d227345 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226485, d227345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d226485, d227345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d226499 q = 0) : d227359 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d226499, d227359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d226499, d227359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22418 (p : Pattern) (selected : d226512 p = 0) : d227372 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226502 q = 0) : d227362 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226502, d227362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226502, d227362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2828 q selected
  have h2 (q : Pattern) (selected : d226503 q = 0) : d227363 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226503, d227363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2828 q selected
    | true =>
      simp only [d226503, d227363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226504 q = 0) : d227364 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226504, d227364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226504, d227364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226505 q = 0) : d227365 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226505, d227365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226505, d227365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226506 q = 0) : d227366 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226506, d227366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226506, d227366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226507 q = 0) : d227367 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226507, d227367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226507, d227367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6764 q selected
  have h7 (q : Pattern) (selected : d226508 q = 0) : d227368 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226508, d227368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6764 q selected
    | true =>
      simp only [d226508, d227368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d226509 q = 0) : d227369 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226509, d227369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d226509, d227369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d226510 q = 0) : d227370 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226510, d227370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d226510, d227370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d226511 q = 0) : d227371 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226511, d227371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d226511, d227371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d226512 q = 0) : d227372 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d226512, d227372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226512, d227372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22419 (p : Pattern) (selected : d226517 p = 0) : d227377 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226483 q = 0) : d227343 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226483, d227343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22414 q selected
    | true =>
      simp only [d226483, d227343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22415 q selected
  have h2 (q : Pattern) (selected : d226484 q = 0) : d227344 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226484, d227344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226484, d227344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226487 q = 0) : d227347 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226487, d227347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22415 q selected
    | true =>
      simp only [d226487, d227347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22416 q selected
  have h4 (q : Pattern) (selected : d226488 q = 0) : d227348 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226488, d227348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226488, d227348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d226489 q = 0) : d227349 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d226489, d227349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226489, d227349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d226500 q = 0) : d227360 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226500, d227360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22415 q selected
    | true =>
      simp only [d226500, d227360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22417 q selected
  have h7 (q : Pattern) (selected : d226501 q = 0) : d227361 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226501, d227361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226501, d227361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d226513 q = 0) : d227373 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226513, d227373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22417 q selected
    | true =>
      simp only [d226513, d227373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22418 q selected
  have h9 (q : Pattern) (selected : d226514 q = 0) : d227374 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226514, d227374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226514, d227374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d226515 q = 0) : d227375 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d226515, d227375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d226515, d227375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d226516 q = 0) : d227376 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d226516, d227376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226516, d227376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d226517 q = 0) : d227377 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d226517, d227377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d226517, d227377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h12 p selected
theorem eqIntro22420 (p : Pattern) (selected : d226522 p = 0) : d227382 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226500 q = 0) : d227360 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226500, d227360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22415 q selected
    | true =>
      simp only [d226500, d227360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22417 q selected
  have h2 (q : Pattern) (selected : d226501 q = 0) : d227361 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226501, d227361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226501, d227361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226513 q = 0) : d227373 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226513, d227373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22417 q selected
    | true =>
      simp only [d226513, d227373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22418 q selected
  have h4 (q : Pattern) (selected : d226514 q = 0) : d227374 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226514, d227374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226514, d227374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d226515 q = 0) : d227375 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d226515, d227375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226515, d227375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d226520 q = 0) : d227380 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d226520, d227380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226520, d227380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d226521 q = 0) : d227381 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d226521, d227381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226521, d227381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d226522 q = 0) : d227382 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d226522, d227382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d226522, d227382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22421 (p : Pattern) (selected : d226528 p = 0) : d227388 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226518 q = 0) : d227378 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d226518, d227378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22419 q selected
    | true =>
      simp only [d226518, d227378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d226519 q = 0) : d227379 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d226519, d227379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226519, d227379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226523 q = 0) : d227383 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d226523, d227383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22420 q selected
    | true =>
      simp only [d226523, d227383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d226524 q = 0) : d227384 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d226524, d227384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226524, d227384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d226525 q = 0) : d227385 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d226525, d227385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226525, d227385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d226526 q = 0) : d227386 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d226526, d227386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226526, d227386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d226527 q = 0) : d227387 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d226527, d227387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d226527, d227387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d226528 q = 0) : d227388 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d226528, d227388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d226528, d227388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22422 (p : Pattern) (selected : d226534 p = 0) : d227394 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226529 q = 0) : d227389 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226529, d227389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226529, d227389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro559 q selected
  have h2 (q : Pattern) (selected : d226530 q = 0) : d227390 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226530, d227390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro559 q selected
    | true =>
      simp only [d226530, d227390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226531 q = 0) : d227391 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226531, d227391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226531, d227391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226532 q = 0) : d227392 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226532, d227392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226532, d227392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226533 q = 0) : d227393 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226533, d227393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226533, d227393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226507 q = 0) : d227367 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226507, d227367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226507, d227367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6764 q selected
  have h7 (q : Pattern) (selected : d226508 q = 0) : d227368 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226508, d227368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6764 q selected
    | true =>
      simp only [d226508, d227368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d226509 q = 0) : d227369 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226509, d227369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d226509, d227369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d226510 q = 0) : d227370 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226510, d227370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d226510, d227370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d226511 q = 0) : d227371 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226511, d227371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d226511, d227371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d226534 q = 0) : d227394 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d226534, d227394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226534, d227394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22423 (p : Pattern) (selected : d226539 p = 0) : d227399 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226535 q = 0) : d227395 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226535, d227395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22417 q selected
    | true =>
      simp only [d226535, d227395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22422 q selected
  have h2 (q : Pattern) (selected : d226536 q = 0) : d227396 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226536, d227396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226536, d227396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226537 q = 0) : d227397 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d226537, d227397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226537, d227397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d226538 q = 0) : d227398 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d226538, d227398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226538, d227398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226539 q = 0) : d227399 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d226539, d227399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226539, d227399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro22424 (p : Pattern) (selected : d226545 p = 0) : d227405 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226523 q = 0) : d227383 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d226523, d227383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22420 q selected
    | true =>
      simp only [d226523, d227383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d226524 q = 0) : d227384 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d226524, d227384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226524, d227384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226540 q = 0) : d227400 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d226540, d227400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22423 q selected
    | true =>
      simp only [d226540, d227400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d226541 q = 0) : d227401 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d226541, d227401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226541, d227401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d226542 q = 0) : d227402 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d226542, d227402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226542, d227402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d226543 q = 0) : d227403 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d226543, d227403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226543, d227403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d226544 q = 0) : d227404 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d226544, d227404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d226544, d227404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d226545 q = 0) : d227405 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d226545, d227405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d226545, d227405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22425 (p : Pattern) (selected : d226565 p = 0) : d227342 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226547 q = 0) : d227328 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226547, d227328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226547, d227328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro587 q selected
  have h2 (q : Pattern) (selected : d226548 q = 0) : d227329 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226548, d227329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro587 q selected
    | true =>
      simp only [d226548, d227329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226549 q = 0) : d227330 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226549, d227330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226549, d227330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226550 q = 0) : d227331 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226550, d227331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226550, d227331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226551 q = 0) : d227332 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226551, d227332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226551, d227332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6772 q selected
  have h6 (q : Pattern) (selected : d226552 q = 0) : d227333 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226552, d227333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6772 q selected
    | true =>
      simp only [d226552, d227333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d226553 q = 0) : d227334 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226553, d227334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226553, d227334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d226554 q = 0) : d227335 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226554, d227335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d226554, d227335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d226555 q = 0) : d227336 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226555, d227336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226555, d227336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d226556 q = 0) : d227322 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226556, d227322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226556, d227322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6773 q selected
  have h11 (q : Pattern) (selected : d226557 q = 0) : d227323 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226557, d227323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6773 q selected
    | true =>
      simp only [d226557, d227323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d226558 q = 0) : d227324 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226558, d227324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d226558, d227324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d226559 q = 0) : d227325 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226559, d227325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d226559, d227325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d226560 q = 0) : d227337 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226560, d227337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226560, d227337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6774 q selected
  have h15 (q : Pattern) (selected : d226561 q = 0) : d227338 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226561, d227338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6774 q selected
    | true =>
      simp only [d226561, d227338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d226562 q = 0) : d227339 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226562, d227339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d226562, d227339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d226563 q = 0) : d227340 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226563, d227340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d226563, d227340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d226564 q = 0) : d227341 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226564, d227341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d226564, d227341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d226565 q = 0) : d227342 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d226565, d227342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d226565, d227342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro22426 (p : Pattern) (selected : d226576 p = 0) : d227359 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226566 q = 0) : d227350 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226566, d227350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226566, d227350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro592 q selected
  have h2 (q : Pattern) (selected : d226567 q = 0) : d227351 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226567, d227351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro592 q selected
    | true =>
      simp only [d226567, d227351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226568 q = 0) : d227352 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226568, d227352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226568, d227352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226569 q = 0) : d227353 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226569, d227353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226569, d227353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226570 q = 0) : d227354 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226570, d227354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226570, d227354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6776 q selected
  have h6 (q : Pattern) (selected : d226571 q = 0) : d227355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226571, d227355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6776 q selected
    | true =>
      simp only [d226571, d227355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d226572 q = 0) : d227356 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226572, d227356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226572, d227356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d226573 q = 0) : d227357 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226573, d227357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d226573, d227357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d226574 q = 0) : d227358 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226574, d227358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226574, d227358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d226560 q = 0) : d227337 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226560, d227337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226560, d227337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6774 q selected
  have h11 (q : Pattern) (selected : d226561 q = 0) : d227338 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226561, d227338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6774 q selected
    | true =>
      simp only [d226561, d227338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d226562 q = 0) : d227339 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226562, d227339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d226562, d227339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d226563 q = 0) : d227340 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226563, d227340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d226563, d227340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d226575 q = 0) : d227345 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226575, d227345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d226575, d227345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d226576 q = 0) : d227359 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d226576, d227359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d226576, d227359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22427 (p : Pattern) (selected : d226589 p = 0) : d227372 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226579 q = 0) : d227362 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226579, d227362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226579, d227362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6778 q selected
  have h2 (q : Pattern) (selected : d226580 q = 0) : d227363 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226580, d227363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6778 q selected
    | true =>
      simp only [d226580, d227363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226581 q = 0) : d227364 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226581, d227364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226581, d227364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226582 q = 0) : d227365 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226582, d227365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226582, d227365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226583 q = 0) : d227366 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226583, d227366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226583, d227366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226584 q = 0) : d227367 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226584, d227367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226584, d227367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6779 q selected
  have h7 (q : Pattern) (selected : d226585 q = 0) : d227368 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226585, d227368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6779 q selected
    | true =>
      simp only [d226585, d227368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d226586 q = 0) : d227369 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226586, d227369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d226586, d227369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d226587 q = 0) : d227370 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226587, d227370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d226587, d227370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d226588 q = 0) : d227371 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226588, d227371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d226588, d227371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d226589 q = 0) : d227372 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d226589, d227372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226589, d227372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22428 (p : Pattern) (selected : d226598 p = 0) : d227394 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226593 q = 0) : d227389 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226593, d227389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226593, d227389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro593 q selected
  have h2 (q : Pattern) (selected : d226594 q = 0) : d227390 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226594, d227390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro593 q selected
    | true =>
      simp only [d226594, d227390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226595 q = 0) : d227391 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226595, d227391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226595, d227391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226596 q = 0) : d227392 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226596, d227392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226596, d227392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226597 q = 0) : d227393 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226597, d227393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226597, d227393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226584 q = 0) : d227367 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226584, d227367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226584, d227367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6779 q selected
  have h7 (q : Pattern) (selected : d226585 q = 0) : d227368 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226585, d227368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6779 q selected
    | true =>
      simp only [d226585, d227368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d226586 q = 0) : d227369 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226586, d227369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d226586, d227369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d226587 q = 0) : d227370 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226587, d227370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d226587, d227370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d226588 q = 0) : d227371 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226588, d227371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d226588, d227371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d226598 q = 0) : d227394 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d226598, d227394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226598, d227394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22429 (p : Pattern) (selected : d226603 p = 0) : d227408 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226577 q = 0) : d227360 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226577, d227360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22425 q selected
    | true =>
      simp only [d226577, d227360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22426 q selected
  have h2 (q : Pattern) (selected : d226578 q = 0) : d227361 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226578, d227361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226578, d227361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226590 q = 0) : d227373 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226590, d227373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22426 q selected
    | true =>
      simp only [d226590, d227373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22427 q selected
  have h4 (q : Pattern) (selected : d226591 q = 0) : d227374 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226591, d227374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226591, d227374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d226592 q = 0) : d227375 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d226592, d227375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226592, d227375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d226599 q = 0) : d227395 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226599, d227395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22426 q selected
    | true =>
      simp only [d226599, d227395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22428 q selected
  have h7 (q : Pattern) (selected : d226600 q = 0) : d227396 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226600, d227396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226600, d227396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d226601 q = 0) : d227397 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d226601, d227397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d226601, d227397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d226602 q = 0) : d227407 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d226602, d227407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226602, d227407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d226603 q = 0) : d227408 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d226603, d227408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d226603, d227408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22430 (p : Pattern) (selected : d226607 p = 0) : d227399 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226599 q = 0) : d227395 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226599, d227395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22426 q selected
    | true =>
      simp only [d226599, d227395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22428 q selected
  have h2 (q : Pattern) (selected : d226600 q = 0) : d227396 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226600, d227396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226600, d227396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226601 q = 0) : d227397 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d226601, d227397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226601, d227397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d226606 q = 0) : d227398 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d226606, d227398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226606, d227398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226607 q = 0) : d227399 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d226607, d227399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226607, d227399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro22431 (p : Pattern) (selected : d226613 p = 0) : d227414 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226604 q = 0) : d227409 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d226604, d227409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22429 q selected
    | true =>
      simp only [d226604, d227409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d226605 q = 0) : d227410 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d226605, d227410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226605, d227410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226608 q = 0) : d227400 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d226608, d227400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22430 q selected
    | true =>
      simp only [d226608, d227400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d226609 q = 0) : d227401 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d226609, d227401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226609, d227401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d226610 q = 0) : d227411 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d226610, d227411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226610, d227411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d226611 q = 0) : d227412 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d226611, d227412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226611, d227412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d226612 q = 0) : d227413 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d226612, d227413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d226612, d227413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d226613 q = 0) : d227414 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d226613, d227414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d226613, d227414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22432 (p : Pattern) (selected : d226617 p = 0) : d227418 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226608 q = 0) : d227400 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d226608, d227400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22430 q selected
    | true =>
      simp only [d226608, d227400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d226609 q = 0) : d227401 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d226609, d227401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226609, d227401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226614 q = 0) : d227415 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d226614, d227415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226614, d227415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d226615 q = 0) : d227416 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d226615, d227416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226615, d227416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226616 q = 0) : d227417 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d226616, d227417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226616, d227417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226617 q = 0) : d227418 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d226617, d227418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226617, d227418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22433 (p : Pattern) (selected : d226620 p = 0) : d227421 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226529 q = 0) : d227389 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226529, d227389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226529, d227389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro559 q selected
  have h2 (q : Pattern) (selected : d226530 q = 0) : d227390 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226530, d227390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro559 q selected
    | true =>
      simp only [d226530, d227390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226531 q = 0) : d227391 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226531, d227391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226531, d227391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226532 q = 0) : d227392 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226532, d227392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226532, d227392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226533 q = 0) : d227393 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226533, d227393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226533, d227393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226620 q = 0) : d227421 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d226620, d227421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226620, d227421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22434 (p : Pattern) (selected : d226625 p = 0) : d227426 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226500 q = 0) : d227360 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226500, d227360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22415 q selected
    | true =>
      simp only [d226500, d227360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22417 q selected
  have h2 (q : Pattern) (selected : d226501 q = 0) : d227361 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226501, d227361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226501, d227361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226513 q = 0) : d227373 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226513, d227373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22417 q selected
    | true =>
      simp only [d226513, d227373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22418 q selected
  have h4 (q : Pattern) (selected : d226514 q = 0) : d227374 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226514, d227374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226514, d227374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d226515 q = 0) : d227375 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d226515, d227375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226515, d227375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d226621 q = 0) : d227422 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226621, d227422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22417 q selected
    | true =>
      simp only [d226621, d227422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22433 q selected
  have h7 (q : Pattern) (selected : d226622 q = 0) : d227423 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226622, d227423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226622, d227423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d226623 q = 0) : d227424 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d226623, d227424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d226623, d227424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d226624 q = 0) : d227425 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d226624, d227425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226624, d227425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d226625 q = 0) : d227426 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d226625, d227426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d226625, d227426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22435 (p : Pattern) (selected : d226631 p = 0) : d227432 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226626 q = 0) : d227427 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d226626, d227427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22434 q selected
    | true =>
      simp only [d226626, d227427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d226627 q = 0) : d227428 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d226627, d227428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226627, d227428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226628 q = 0) : d227429 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d226628, d227429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226628, d227429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d226629 q = 0) : d227430 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d226629, d227430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226629, d227430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226630 q = 0) : d227431 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d226630, d227431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226630, d227431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226631 q = 0) : d227432 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d226631, d227432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226631, d227432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22436 (p : Pattern) (selected : d226637 p = 0) : d227438 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226546 q = 0) : d227406 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d226546, d227406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22421 q selected
    | true =>
      simp only [d226546, d227406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22424 q selected
  have h2 (q : Pattern) (selected : d226618 q = 0) : d227419 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d226618, d227419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22431 q selected
    | true =>
      simp only [d226618, d227419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22432 q selected
  have h3 (q : Pattern) (selected : d226619 q = 0) : d227420 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d226619, d227420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226619, d227420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226632 q = 0) : d227433 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d226632, d227433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22435 q selected
    | true =>
      simp only [d226632, d227433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226633 q = 0) : d227434 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d226633, d227434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226633, d227434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226634 q = 0) : d227435 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d226634, d227435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226634, d227435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d226635 q = 0) : d227436 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d226635, d227436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226635, d227436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d226636 q = 0) : d227437 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d226636, d227437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226636, d227437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d226637 q = 0) : d227438 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d226637, d227438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226637, d227438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro22437 (p : Pattern) (selected : d226642 p = 0) : d227418 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226540 q = 0) : d227400 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d226540, d227400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22423 q selected
    | true =>
      simp only [d226540, d227400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d226541 q = 0) : d227401 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d226541, d227401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226541, d227401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226639 q = 0) : d227415 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d226639, d227415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226639, d227415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d226640 q = 0) : d227416 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d226640, d227416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226640, d227416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226641 q = 0) : d227417 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d226641, d227417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226641, d227417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226642 q = 0) : d227418 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d226642, d227418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226642, d227418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22438 (p : Pattern) (selected : d226648 p = 0) : d227445 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226643 q = 0) : d227440 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d226643, d227440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22437 q selected
    | true =>
      simp only [d226643, d227440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d226644 q = 0) : d227441 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d226644, d227441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226644, d227441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226645 q = 0) : d227442 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d226645, d227442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226645, d227442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d226646 q = 0) : d227443 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d226646, d227443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226646, d227443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d226647 q = 0) : d227444 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d226647, d227444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226647, d227444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d226648 q = 0) : d227445 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d226648, d227445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226648, d227445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22439 (p : Pattern) (selected : d226654 p = 0) : d227451 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226638 q = 0) : d227439 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d226638, d227439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226638, d227439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22436 q selected
  have h2 (q : Pattern) (selected : d226649 q = 0) : d227446 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d226649, d227446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226649, d227446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22438 q selected
  have h3 (q : Pattern) (selected : d226650 q = 0) : d227447 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d226650, d227447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226650, d227447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226651 q = 0) : d227448 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d226651, d227448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226651, d227448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226652 q = 0) : d227449 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d226652, d227449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226652, d227449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226653 q = 0) : d227450 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d226653, d227450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226653, d227450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d226654 q = 0) : d227451 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d226654, d227451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226654, d227451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro22440 (p : Pattern) (selected : d226660 p = 0) : d227457 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226655 q = 0) : d227452 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d226655, d227452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226655, d227452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22439 q selected
  have h2 (q : Pattern) (selected : d226656 q = 0) : d227453 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d226656, d227453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226656, d227453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226657 q = 0) : d227454 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d226657, d227454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226657, d227454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226658 q = 0) : d227455 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d226658, d227455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226658, d227455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d226659 q = 0) : d227456 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d226659, d227456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226659, d227456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d226660 q = 0) : d227457 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d226660, d227457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226660, d227457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22441 (p : Pattern) (selected : d226666 p = 0) : d227463 p = 1 := by
  have h0 (q : Pattern) (selected : d225879 q = 0) : d226906 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d225879, d226906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22318 q selected
    | true =>
      simp only [d225879, d226906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22336 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d226018 q = 0) : d227000 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d226018, d227000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226018, d227000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22359 q selected
  have h3 (q : Pattern) (selected : d226019 q = 0) : d227001 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d226019, d227001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226019, d227001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226229 q = 0) : d227152 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d226229, d227152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226229, d227152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22386 q selected
  have h5 (q : Pattern) (selected : d226230 q = 0) : d227153 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d226230, d227153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226230, d227153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d226231 q = 0) : d227154 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d226231, d227154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226231, d227154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d226449 q = 0) : d227309 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d226449, d227309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226449, d227309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22413 q selected
  have h8 (q : Pattern) (selected : d226450 q = 0) : d227310 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d226450, d227310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226450, d227310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d226451 q = 0) : d227311 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d226451, d227311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226451, d227311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d226452 q = 0) : d227312 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d226452, d227312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d226452, d227312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d226661 q = 0) : d227458 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d226661, d227458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226661, d227458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22440 q selected
  have h12 (q : Pattern) (selected : d226662 q = 0) : d227459 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d226662, d227459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226662, d227459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d226663 q = 0) : d227460 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d226663, d227460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226663, d227460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d226664 q = 0) : d227461 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d226664, d227461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226664, d227461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d226665 q = 0) : d227462 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d226665, d227462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d226665, d227462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d226666 q = 0) : d227463 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d226666, d227463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d226666, d227463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro22442 (p : Pattern) (selected : d226672 p = 0) : d227469 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226667 q = 0) : d227464 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d226667, d227464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22441 q selected
    | true =>
      simp only [d226667, d227464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d226668 q = 0) : d227465 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d226668, d227465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226668, d227465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226669 q = 0) : d227466 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d226669, d227466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226669, d227466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d226670 q = 0) : d227467 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d226670, d227467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226670, d227467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226671 q = 0) : d227468 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d226671, d227468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226671, d227468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226672 q = 0) : d227469 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d226672, d227469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226672, d227469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22443 (p : Pattern) (selected : d226678 p = 0) : d227475 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226673 q = 0) : d227470 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d226673, d227470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22442 q selected
    | true =>
      simp only [d226673, d227470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d226674 q = 0) : d227471 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d226674, d227471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226674, d227471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226675 q = 0) : d227472 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d226675, d227472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226675, d227472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d226676 q = 0) : d227473 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d226676, d227473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226676, d227473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226677 q = 0) : d227474 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d226677, d227474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226677, d227474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226678 q = 0) : d227475 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d226678, d227475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226678, d227475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22444 (p : Pattern) (selected : d226684 p = 0) : d227481 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226679 q = 0) : d227476 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d226679, d227476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22443 q selected
    | true =>
      simp only [d226679, d227476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d226680 q = 0) : d227477 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d226680, d227477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226680, d227477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226681 q = 0) : d227478 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d226681, d227478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226681, d227478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d226682 q = 0) : d227479 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d226682, d227479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226682, d227479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226683 q = 0) : d227480 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d226683, d227480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226683, d227480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226684 q = 0) : d227481 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d226684, d227481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226684, d227481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22445 (p : Pattern) (selected : d226690 p = 0) : d227487 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226685 q = 0) : d227482 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d226685, d227482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22444 q selected
    | true =>
      simp only [d226685, d227482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d226686 q = 0) : d227483 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d226686, d227483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226686, d227483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226687 q = 0) : d227484 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d226687, d227484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226687, d227484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d226688 q = 0) : d227485 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d226688, d227485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226688, d227485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226689 q = 0) : d227486 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d226689, d227486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226689, d227486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226690 q = 0) : d227487 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d226690, d227487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226690, d227487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22446 (p : Pattern) (selected : d226696 p = 0) : d227493 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226691 q = 0) : d227488 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d226691, d227488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22445 q selected
    | true =>
      simp only [d226691, d227488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d226692 q = 0) : d227489 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d226692, d227489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226692, d227489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226693 q = 0) : d227490 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d226693, d227490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226693, d227490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d226694 q = 0) : d227491 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d226694, d227491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226694, d227491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226695 q = 0) : d227492 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d226695, d227492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226695, d227492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226696 q = 0) : d227493 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d226696, d227493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226696, d227493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22447 (p : Pattern) (selected : d226702 p = 0) : d227499 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226697 q = 0) : d227494 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d226697, d227494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22446 q selected
    | true =>
      simp only [d226697, d227494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d226698 q = 0) : d227495 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d226698, d227495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226698, d227495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226699 q = 0) : d227496 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d226699, d227496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226699, d227496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d226700 q = 0) : d227497 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d226700, d227497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226700, d227497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226701 q = 0) : d227498 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d226701, d227498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226701, d227498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226702 q = 0) : d227499 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d226702, d227499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226702, d227499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22448 (p : Pattern) (selected : d226708 p = 0) : d227505 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226703 q = 0) : d227500 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d226703, d227500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22447 q selected
    | true =>
      simp only [d226703, d227500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d226704 q = 0) : d227501 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d226704, d227501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226704, d227501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226705 q = 0) : d227502 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d226705, d227502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226705, d227502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d226706 q = 0) : d227503 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d226706, d227503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226706, d227503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226707 q = 0) : d227504 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d226707, d227504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226707, d227504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226708 q = 0) : d227505 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d226708, d227505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226708, d227505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22449 (p : Pattern) (selected : d225671 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d225666 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1 q selected
  have h2 (q : Pattern) (selected : d225667 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1 q selected
    | true =>
      simp only [d225667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d225668 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d225668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d225669 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225670 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d225670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d225671 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d225671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22450 (p : Pattern) (selected : d225676 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d225672 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d225672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22449 q selected
    | true =>
      simp only [d225672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d225673 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d225673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d225674 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d225674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d225674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d225675 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d225675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225676 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d225676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro22451 (p : Pattern) (selected : d225682 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d225677 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d225677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22450 q selected
    | true =>
      simp only [d225677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d225678 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d225678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d225679 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d225679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d225679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d225680 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d225680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225681 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d225681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d225682 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d225682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22452 (p : Pattern) (selected : d225688 p = 1) : d227510 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d225665 q = 1) : d225665 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d225683 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d225683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22451 q selected
    | true =>
      simp only [d225683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d225684 q = 1) : d227506 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d225684, d227506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d225684, d227506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d225633 q = 1) : d225633 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d225685 q = 1) : d227507 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d225685, d227507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225685, d227507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d225686 q = 1) : d227508 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d225686, d227508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225686, d227508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d225687 q = 1) : d227509 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d225687, d227509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225687, d227509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d225688 q = 1) : d227510 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d225688, d227510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225688, d227510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22453 (p : Pattern) (selected : d225694 p = 1) : d227516 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d225689 q = 1) : d227511 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d225689, d227511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225689, d227511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22452 q selected
  have h2 (q : Pattern) (selected : d225690 q = 1) : d227512 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d225690, d227512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d225690, d227512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d225691 q = 1) : d227513 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d225691, d227513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d225691, d227513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d225692 q = 1) : d227514 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d225692, d227514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225692, d227514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225693 q = 1) : d227515 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d225693, d227515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225693, d227515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d225694 q = 1) : d227516 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d225694, d227516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225694, d227516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22454 (p : Pattern) (selected : d225728 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d225723 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15 q selected
  have h2 (q : Pattern) (selected : d225724 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15 q selected
    | true =>
      simp only [d225724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d225725 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d225725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d225726 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225666 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1 q selected
  have h6 (q : Pattern) (selected : d225667 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1 q selected
    | true =>
      simp only [d225667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d225668 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d225669 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d225669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d225727 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d225727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d225670 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d225670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d225670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d225728 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d225728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d225728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22455 (p : Pattern) (selected : d225733 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d225729 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d225729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22454 q selected
    | true =>
      simp only [d225729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22449 q selected
  have h2 (q : Pattern) (selected : d225730 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d225730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d225672 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d225672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22449 q selected
    | true =>
      simp only [d225672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d225673 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d225673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d225731 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d225731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d225731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d225674 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d225674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d225732 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d225732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d225733 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d225733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d225733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22456 (p : Pattern) (selected : d225739 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d225734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d225734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22455 q selected
    | true =>
      simp only [d225734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d225735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d225735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d225677 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d225677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22450 q selected
    | true =>
      simp only [d225677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d225678 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d225678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d225736 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d225736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d225736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d225737 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d225737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d225738 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d225738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d225738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d225739 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d225739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d225739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22457 (p : Pattern) (selected : d225751 p = 1) : d227526 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d225722 q = 1) : d225722 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d225740 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d225740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22456 q selected
    | true =>
      simp only [d225740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22451 q selected
  have h3 (q : Pattern) (selected : d225741 q = 1) : d227522 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d225741, d227522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d225741, d227522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d225747 q = 1) : d225747 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d225748 q = 1) : d227523 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d225748, d227523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225748, d227523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d225749 q = 1) : d227524 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d225749, d227524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225749, d227524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d225750 q = 1) : d227525 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d225750, d227525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225750, d227525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d225751 q = 1) : d227526 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d225751, d227526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225751, d227526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22458 (p : Pattern) (selected : d225763 p = 1) : d227532 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d225752 q = 1) : d227527 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d225752, d227527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225752, d227527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22457 q selected
  have h2 (q : Pattern) (selected : d225758 q = 1) : d225758 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d225759 q = 1) : d227528 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d225759, d227528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d225759, d227528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d225760 q = 1) : d227529 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d225760, d227529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225760, d227529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225761 q = 1) : d227530 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d225761, d227530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225761, d227530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d225762 q = 1) : d227531 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d225762, d227531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225762, d227531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d225763 q = 1) : d227532 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d225763, d227532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225763, d227532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro22459 (p : Pattern) (selected : d225769 p = 1) : d227538 p = 1 := by
  have h0 (q : Pattern) (selected : d225647 q = 1) : d225647 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d225695 q = 1) : d227517 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d225695, d227517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d225695, d227517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22453 q selected
  have h3 (q : Pattern) (selected : d225696 q = 1) : d227518 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d225696, d227518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d225696, d227518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d225697 q = 1) : d227519 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d225697, d227519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d225697, d227519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d225698 q = 1) : d227520 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d225698, d227520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d225698, d227520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d225699 q = 1) : d227521 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d225699, d227521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225699, d227521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d225764 q = 1) : d227533 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d225764, d227533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d225764, d227533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22458 q selected
  have h8 (q : Pattern) (selected : d225765 q = 1) : d227534 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d225765, d227534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d225765, d227534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d225766 q = 1) : d227535 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d225766, d227535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d225766, d227535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d225767 q = 1) : d227536 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d225767, d227536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d225767, d227536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d225768 q = 1) : d227537 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d225768, d227537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d225768, d227537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d225769 q = 1) : d227538 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d225769, d227538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d225769, d227538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  exact h12 p selected
theorem eqIntro22460 (p : Pattern) (selected : d225823 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d225813 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30 q selected
  have h2 (q : Pattern) (selected : d225814 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30 q selected
    | true =>
      simp only [d225814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d225815 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d225815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d225816 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225723 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15 q selected
  have h6 (q : Pattern) (selected : d225724 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15 q selected
    | true =>
      simp only [d225724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d225725 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d225726 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d225726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d225817 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d225817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d225818 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6813 q selected
  have h11 (q : Pattern) (selected : d225819 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6813 q selected
    | true =>
      simp only [d225819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d225820 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d225820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d225821 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d225821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d225666 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1 q selected
  have h15 (q : Pattern) (selected : d225667 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1 q selected
    | true =>
      simp only [d225667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d225668 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d225668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d225669 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d225669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d225822 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d225822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d225822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d225823 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d225823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d225823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro22461 (p : Pattern) (selected : d225829 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d225824 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d225824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22460 q selected
    | true =>
      simp only [d225824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22454 q selected
  have h2 (q : Pattern) (selected : d225825 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d225825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d225729 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d225729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22454 q selected
    | true =>
      simp only [d225729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22449 q selected
  have h4 (q : Pattern) (selected : d225730 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d225730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d225826 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d225826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d225826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d225827 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d225827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d225828 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d225828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d225829 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d225829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d225829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22462 (p : Pattern) (selected : d225833 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d225729 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d225729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22454 q selected
    | true =>
      simp only [d225729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22449 q selected
  have h2 (q : Pattern) (selected : d225730 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d225730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d225827 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d225827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d225827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d225832 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d225832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225833 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d225833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro22463 (p : Pattern) (selected : d225839 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d225830 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d225830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22461 q selected
    | true =>
      simp only [d225830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d225831 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d225831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d225834 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d225834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22462 q selected
    | true =>
      simp only [d225834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d225835 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d225835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d225836 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d225836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d225836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d225837 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d225837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d225838 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d225838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d225838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d225839 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d225839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d225839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22464 (p : Pattern) (selected : d225843 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d225834 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d225834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22462 q selected
    | true =>
      simp only [d225834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d225835 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d225835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d225840 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d225840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d225840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d225841 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d225841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225842 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d225842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d225843 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d225843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22465 (p : Pattern) (selected : d225855 p = 1) : d227543 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d225812 q = 1) : d225812 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d225844 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d225844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22463 q selected
    | true =>
      simp only [d225844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22464 q selected
  have h3 (q : Pattern) (selected : d225845 q = 1) : d227539 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d225845, d227539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d225845, d227539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d225851 q = 1) : d225851 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d225852 q = 1) : d227540 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d225852, d227540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225852, d227540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d225853 q = 1) : d227541 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d225853, d227541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225853, d227541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d225854 q = 1) : d227542 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d225854, d227542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225854, d227542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d225855 q = 1) : d227543 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d225855, d227543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225855, d227543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22466 (p : Pattern) (selected : d225872 p = 1) : d227549 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d225856 q = 1) : d227544 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d225856, d227544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225856, d227544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22465 q selected
  have h2 (q : Pattern) (selected : d225867 q = 1) : d225867 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d225868 q = 1) : d227545 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d225868, d227545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d225868, d227545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d225869 q = 1) : d227546 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d225869, d227546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225869, d227546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225870 q = 1) : d227547 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d225870, d227547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225870, d227547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d225871 q = 1) : d227548 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d225871, d227548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225871, d227548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d225872 q = 1) : d227549 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d225872, d227549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225872, d227549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro22467 (p : Pattern) (selected : d225878 p = 1) : d227555 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d225873 q = 1) : d227550 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d225873, d227550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225873, d227550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22466 q selected
  have h2 (q : Pattern) (selected : d225874 q = 1) : d227551 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d225874, d227551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225874, d227551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d225875 q = 1) : d227552 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d225875, d227552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225875, d227552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d225876 q = 1) : d227553 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d225876, d227553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225876, d227553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d225877 q = 1) : d227554 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d225877, d227554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225877, d227554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d225878 q = 1) : d227555 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d225878, d227555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225878, d227555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22468 (p : Pattern) (selected : d225956 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d225938 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro51 q selected
  have h2 (q : Pattern) (selected : d225939 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro51 q selected
    | true =>
      simp only [d225939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d225940 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d225940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d225941 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225942 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6823 q selected
  have h6 (q : Pattern) (selected : d225943 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6823 q selected
    | true =>
      simp only [d225943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d225944 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d225945 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d225945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d225946 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d225946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d225947 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6824 q selected
  have h11 (q : Pattern) (selected : d225948 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6824 q selected
    | true =>
      simp only [d225948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d225949 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d225949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d225950 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d225950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d225951 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro52 q selected
  have h15 (q : Pattern) (selected : d225952 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro52 q selected
    | true =>
      simp only [d225952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d225953 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d225953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d225954 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d225954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d225955 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d225955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d225955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d225956 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d225956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d225956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro22469 (p : Pattern) (selected : d225959 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d225813 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30 q selected
  have h2 (q : Pattern) (selected : d225814 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30 q selected
    | true =>
      simp only [d225814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d225815 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d225815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d225816 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225951 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro52 q selected
  have h6 (q : Pattern) (selected : d225952 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro52 q selected
    | true =>
      simp only [d225952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d225953 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d225954 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d225954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d225957 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d225957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d225958 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d225958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d225958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d225959 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d225959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d225959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22470 (p : Pattern) (selected : d225962 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d225951 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro52 q selected
  have h2 (q : Pattern) (selected : d225952 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d225952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro52 q selected
    | true =>
      simp only [d225952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d225953 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d225953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d225953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d225954 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d225954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225958 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d225958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d225962 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d225962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22471 (p : Pattern) (selected : d225968 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d225960 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d225960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22468 q selected
    | true =>
      simp only [d225960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22469 q selected
  have h2 (q : Pattern) (selected : d225961 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d225961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d225963 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d225963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22469 q selected
    | true =>
      simp only [d225963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22470 q selected
  have h4 (q : Pattern) (selected : d225964 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d225964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d225965 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d225965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d225965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d225966 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d225966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d225967 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d225967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d225968 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d225968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d225968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22472 (p : Pattern) (selected : d225972 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d225963 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d225963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22469 q selected
    | true =>
      simp only [d225963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22470 q selected
  have h2 (q : Pattern) (selected : d225964 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d225964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d225966 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d225966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d225966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d225971 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d225971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225972 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d225972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro22473 (p : Pattern) (selected : d225978 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d225969 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d225969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22471 q selected
    | true =>
      simp only [d225969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d225970 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d225970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d225973 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d225973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22472 q selected
    | true =>
      simp only [d225973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d225974 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d225974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d225975 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d225975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d225975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d225976 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d225976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d225977 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d225977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d225977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d225978 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d225978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d225978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22474 (p : Pattern) (selected : d225982 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d225973 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d225973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22472 q selected
    | true =>
      simp only [d225973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d225974 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d225974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d225979 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d225979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d225979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d225980 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d225980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d225981 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d225981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d225981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d225982 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d225982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d225982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22475 (p : Pattern) (selected : d225994 p = 1) : d227561 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d225937 q = 1) : d225937 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d225983 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d225983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22473 q selected
    | true =>
      simp only [d225983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22474 q selected
  have h3 (q : Pattern) (selected : d225984 q = 1) : d227557 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d225984, d227557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d225984, d227557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d225990 q = 1) : d225990 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d225991 q = 1) : d227558 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d225991, d227558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d225991, d227558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d225992 q = 1) : d227559 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d225992, d227559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225992, d227559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d225993 q = 1) : d227560 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d225993, d227560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225993, d227560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d225994 q = 1) : d227561 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d225994, d227561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225994, d227561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22476 (p : Pattern) (selected : d226011 p = 1) : d227567 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d225995 q = 1) : d227562 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d225995, d227562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d225995, d227562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22475 q selected
  have h2 (q : Pattern) (selected : d226006 q = 1) : d226006 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d226007 q = 1) : d227563 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d226007, d227563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226007, d227563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226008 q = 1) : d227564 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d226008, d227564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226008, d227564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226009 q = 1) : d227565 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d226009, d227565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226009, d227565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226010 q = 1) : d227566 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d226010, d227566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226010, d227566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d226011 q = 1) : d227567 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d226011, d227567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226011, d227567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro22477 (p : Pattern) (selected : d226017 p = 1) : d227573 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d226012 q = 1) : d227568 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d226012, d227568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226012, d227568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22476 q selected
  have h2 (q : Pattern) (selected : d226013 q = 1) : d227569 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d226013, d227569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226013, d227569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226014 q = 1) : d227570 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d226014, d227570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226014, d227570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226015 q = 1) : d227571 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d226015, d227571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226015, d227571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d226016 q = 1) : d227572 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d226016, d227572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226016, d227572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d226017 q = 1) : d227573 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d226017, d227573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226017, d227573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22478 (p : Pattern) (selected : d226137 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d226119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro79 q selected
  have h2 (q : Pattern) (selected : d226120 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro79 q selected
    | true =>
      simp only [d226120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226121 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226122 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226123 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6837 q selected
  have h6 (q : Pattern) (selected : d226124 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6837 q selected
    | true =>
      simp only [d226124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d226125 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d226126 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d226126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d226127 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d226128 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6838 q selected
  have h11 (q : Pattern) (selected : d226129 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6838 q selected
    | true =>
      simp only [d226129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d226130 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d226130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d226131 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d226131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d226132 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6839 q selected
  have h15 (q : Pattern) (selected : d226133 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6839 q selected
    | true =>
      simp only [d226133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d226134 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d226134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d226135 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d226135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d226136 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d226136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d226137 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d226137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d226137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro22479 (p : Pattern) (selected : d226148 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d226138 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro80 q selected
  have h2 (q : Pattern) (selected : d226139 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro80 q selected
    | true =>
      simp only [d226139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226140 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226141 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226142 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro81 q selected
  have h6 (q : Pattern) (selected : d226143 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro81 q selected
    | true =>
      simp only [d226143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d226144 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d226145 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d226145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d226146 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d226132 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6839 q selected
  have h11 (q : Pattern) (selected : d226133 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6839 q selected
    | true =>
      simp only [d226133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d226134 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d226134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d226135 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d226135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d226147 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d226147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d226148 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d226148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d226148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22480 (p : Pattern) (selected : d226161 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d226151 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6842 q selected
  have h2 (q : Pattern) (selected : d226152 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6842 q selected
    | true =>
      simp only [d226152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226153 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226154 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226155 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226156 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6843 q selected
  have h7 (q : Pattern) (selected : d226157 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6843 q selected
    | true =>
      simp only [d226157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d226158 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d226158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d226159 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d226159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d226160 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d226160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d226161 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d226161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22481 (p : Pattern) (selected : d226166 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d226142 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro81 q selected
  have h2 (q : Pattern) (selected : d226143 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro81 q selected
    | true =>
      simp only [d226143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226144 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226145 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226165 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226156 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6843 q selected
  have h7 (q : Pattern) (selected : d226157 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6843 q selected
    | true =>
      simp only [d226157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d226158 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d226158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d226159 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d226159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d226160 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d226160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d226166 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d226166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22482 (p : Pattern) (selected : d226171 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d226149 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22478 q selected
    | true =>
      simp only [d226149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22479 q selected
  have h2 (q : Pattern) (selected : d226150 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226162 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22479 q selected
    | true =>
      simp only [d226162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22480 q selected
  have h4 (q : Pattern) (selected : d226163 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d226164 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d226164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d226167 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22479 q selected
    | true =>
      simp only [d226167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22481 q selected
  have h7 (q : Pattern) (selected : d226168 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d226169 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d226169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d226169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d226170 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d226170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d226171 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d226171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d226171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22483 (p : Pattern) (selected : d226175 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d226167 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22479 q selected
    | true =>
      simp only [d226167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22481 q selected
  have h2 (q : Pattern) (selected : d226168 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226169 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d226169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d226174 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d226174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226175 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d226175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro22484 (p : Pattern) (selected : d226181 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d226172 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d226172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22482 q selected
    | true =>
      simp only [d226172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d226173 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d226173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226176 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d226176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22483 q selected
    | true =>
      simp only [d226176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d226177 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d226177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d226178 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d226178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d226179 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d226179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d226180 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d226180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d226180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d226181 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d226181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d226181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22485 (p : Pattern) (selected : d226185 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d226176 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d226176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22483 q selected
    | true =>
      simp only [d226176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d226177 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d226177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226182 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d226182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d226183 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d226183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226184 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d226184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226185 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d226185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22486 (p : Pattern) (selected : d226205 p = 1) : d227580 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d226118 q = 1) : d226118 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d226186 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d226186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22484 q selected
    | true =>
      simp only [d226186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22485 q selected
  have h3 (q : Pattern) (selected : d226187 q = 1) : d227576 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d226187, d227576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226187, d227576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226201 q = 1) : d226201 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d226202 q = 1) : d227577 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d226202, d227577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226202, d227577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d226203 q = 1) : d227578 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d226203, d227578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226203, d227578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d226204 q = 1) : d227579 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d226204, d227579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226204, d227579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d226205 q = 1) : d227580 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d226205, d227580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226205, d227580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22487 (p : Pattern) (selected : d226222 p = 1) : d227586 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d226206 q = 1) : d227581 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d226206, d227581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226206, d227581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22486 q selected
  have h2 (q : Pattern) (selected : d226217 q = 1) : d226217 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d226218 q = 1) : d227582 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d226218, d227582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226218, d227582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226219 q = 1) : d227583 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d226219, d227583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226219, d227583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226220 q = 1) : d227584 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d226220, d227584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226220, d227584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226221 q = 1) : d227585 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d226221, d227585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226221, d227585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d226222 q = 1) : d227586 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d226222, d227586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226222, d227586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro22488 (p : Pattern) (selected : d226228 p = 1) : d227592 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d226223 q = 1) : d227587 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d226223, d227587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226223, d227587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22487 q selected
  have h2 (q : Pattern) (selected : d226224 q = 1) : d227588 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d226224, d227588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226224, d227588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226225 q = 1) : d227589 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d226225, d227589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226225, d227589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226226 q = 1) : d227590 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d226226, d227590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226226, d227590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d226227 q = 1) : d227591 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d226227, d227591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226227, d227591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d226228 q = 1) : d227592 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d226228, d227592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226228, d227592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22489 (p : Pattern) (selected : d226353 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d226335 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro113 q selected
  have h2 (q : Pattern) (selected : d226336 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro113 q selected
    | true =>
      simp only [d226336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226337 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226338 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226339 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6855 q selected
  have h6 (q : Pattern) (selected : d226340 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6855 q selected
    | true =>
      simp only [d226340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d226341 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d226342 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d226342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d226343 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d226344 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6856 q selected
  have h11 (q : Pattern) (selected : d226345 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6856 q selected
    | true =>
      simp only [d226345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d226346 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d226346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d226347 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d226347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d226348 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6857 q selected
  have h15 (q : Pattern) (selected : d226349 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6857 q selected
    | true =>
      simp only [d226349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d226350 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d226350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d226351 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d226351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d226352 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d226352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d226353 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d226353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d226353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro22490 (p : Pattern) (selected : d226364 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d226354 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro116 q selected
  have h2 (q : Pattern) (selected : d226355 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro116 q selected
    | true =>
      simp only [d226355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226356 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226357 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226358 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6859 q selected
  have h6 (q : Pattern) (selected : d226359 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6859 q selected
    | true =>
      simp only [d226359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d226360 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d226361 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d226361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d226362 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d226348 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6857 q selected
  have h11 (q : Pattern) (selected : d226349 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6857 q selected
    | true =>
      simp only [d226349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d226350 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d226350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d226351 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d226351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d226363 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d226363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d226364 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d226364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d226364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22491 (p : Pattern) (selected : d226377 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d226367 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6861 q selected
  have h2 (q : Pattern) (selected : d226368 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6861 q selected
    | true =>
      simp only [d226368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226369 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226370 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226371 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226372 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6862 q selected
  have h7 (q : Pattern) (selected : d226373 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6862 q selected
    | true =>
      simp only [d226373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d226374 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d226374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d226375 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d226375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d226376 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d226376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d226377 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d226377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22492 (p : Pattern) (selected : d226386 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d226381 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro117 q selected
  have h2 (q : Pattern) (selected : d226382 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro117 q selected
    | true =>
      simp only [d226382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226383 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226384 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226385 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226372 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6862 q selected
  have h7 (q : Pattern) (selected : d226373 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6862 q selected
    | true =>
      simp only [d226373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d226374 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d226374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d226375 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d226375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d226376 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d226376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d226386 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d226386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22493 (p : Pattern) (selected : d226391 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d226365 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22489 q selected
    | true =>
      simp only [d226365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22490 q selected
  have h2 (q : Pattern) (selected : d226366 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226378 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22490 q selected
    | true =>
      simp only [d226378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22491 q selected
  have h4 (q : Pattern) (selected : d226379 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d226380 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d226380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d226387 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22490 q selected
    | true =>
      simp only [d226387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22492 q selected
  have h7 (q : Pattern) (selected : d226388 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d226389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d226389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d226389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d226390 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d226390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d226391 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d226391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d226391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22494 (p : Pattern) (selected : d226395 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d226387 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22490 q selected
    | true =>
      simp only [d226387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22492 q selected
  have h2 (q : Pattern) (selected : d226388 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d226389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d226394 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d226394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226395 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d226395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro22495 (p : Pattern) (selected : d226401 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d226392 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d226392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22493 q selected
    | true =>
      simp only [d226392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d226393 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d226393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226396 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d226396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22494 q selected
    | true =>
      simp only [d226396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d226397 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d226397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d226398 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d226398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d226399 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d226399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d226400 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d226400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d226400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d226401 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d226401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d226401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22496 (p : Pattern) (selected : d226405 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d226396 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d226396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22494 q selected
    | true =>
      simp only [d226396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d226397 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d226397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226402 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d226402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d226403 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d226403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226404 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d226404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226405 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d226405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22497 (p : Pattern) (selected : d226425 p = 1) : d227600 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d226334 q = 1) : d226334 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d226406 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d226406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22495 q selected
    | true =>
      simp only [d226406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22496 q selected
  have h3 (q : Pattern) (selected : d226407 q = 1) : d227596 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d226407, d227596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226407, d227596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226421 q = 1) : d226421 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d226422 q = 1) : d227597 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d226422, d227597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226422, d227597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d226423 q = 1) : d227598 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d226423, d227598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226423, d227598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d226424 q = 1) : d227599 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d226424, d227599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226424, d227599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d226425 q = 1) : d227600 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d226425, d227600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226425, d227600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22498 (p : Pattern) (selected : d226442 p = 1) : d227606 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d226426 q = 1) : d227601 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d226426, d227601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226426, d227601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22497 q selected
  have h2 (q : Pattern) (selected : d226437 q = 1) : d226437 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d226438 q = 1) : d227602 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d226438, d227602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226438, d227602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226439 q = 1) : d227603 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d226439, d227603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226439, d227603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226440 q = 1) : d227604 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d226440, d227604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226440, d227604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226441 q = 1) : d227605 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d226441, d227605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226441, d227605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d226442 q = 1) : d227606 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d226442, d227606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226442, d227606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro22499 (p : Pattern) (selected : d226448 p = 1) : d227612 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d226443 q = 1) : d227607 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d226443, d227607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226443, d227607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22498 q selected
  have h2 (q : Pattern) (selected : d226444 q = 1) : d227608 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d226444, d227608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226444, d227608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226445 q = 1) : d227609 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d226445, d227609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226445, d227609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226446 q = 1) : d227610 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d226446, d227610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226446, d227610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d226447 q = 1) : d227611 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d226447, d227611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226447, d227611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d226448 q = 1) : d227612 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d226448, d227612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226448, d227612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
end NetHack.Soko22Hazard87
