import NetHack.Soko22Hazard87.AndIntroBlocks0028
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro7250 (p : Pattern) (ha : d4444 p = 1) (hb : d68222 p = 1) : d68600 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4439 q = 1) (hb : d68222 q = 1) : d68595 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d4439, d68595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4439, d68595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7249 q ha hb
  have h2 (q : Pattern) (ha : d4440 q = 1) (hb : d68222 q = 1) : d68596 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d4440, d68596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4440, d68596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4441 q = 1) (hb : d68222 q = 1) : d68597 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d4441, d68597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4441, d68597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4442 q = 1) (hb : d68222 q = 1) : d68598 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d4442, d68598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4442, d68598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4443 q = 1) (hb : d68222 q = 1) : d68599 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d4443, d68599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4443, d68599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4444 q = 1) (hb : d68222 q = 1) : d68600 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d4444, d68600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4444, d68600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7251 (p : Pattern) (ha : d4450 p = 1) (hb : d68222 p = 1) : d68604 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4446 q = 1) (hb : d68221 q = 1) : d4446 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d910 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4447 q = 1) (hb : d68222 q = 1) : d67719 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4447, d68222, d67719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4447, d68222, d67719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4448 q = 1) (hb : d68222 q = 1) : d68602 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4448, d68602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4448, d68602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4449 q = 1) (hb : d68222 q = 1) : d68603 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4449, d68603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4449, d68603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4450 q = 1) (hb : d68222 q = 1) : d68604 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4450, d68604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4450, d68604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7252 (p : Pattern) (ha : d4455 p = 1) (hb : d68222 p = 1) : d68605 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4446 q = 1) (hb : d68221 q = 1) : d4446 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d910 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4447 q = 1) (hb : d68222 q = 1) : d67719 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4447, d68222, d67719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4447, d68222, d67719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4448 q = 1) (hb : d68222 q = 1) : d68602 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4448, d68602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4448, d68602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4449 q = 1) (hb : d68222 q = 1) : d68603 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4449, d68603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4449, d68603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4451 q = 1) (hb : d68221 q = 1) : d4451 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d933 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d4452 q = 1) (hb : d68222 q = 1) : d67723 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4452, d68222, d67723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4452, d68222, d67723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d4453 q = 1) (hb : d68222 q = 1) : d67731 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4453, d67731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4453, d67731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4454 q = 1) (hb : d68222 q = 1) : d67732 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4454, d67732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4454, d67732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4455 q = 1) (hb : d68222 q = 1) : d68605 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4455, d68605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4455, d68605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro7253 (p : Pattern) (ha : d4476 p = 1) (hb : d68222 p = 1) : d68618 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4456 q = 1) (hb : d68222 q = 1) : d68606 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4456, d68606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7251 q ha hb
    | true =>
      simp only [d4456, d68606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7252 q ha hb
  have h2 (q : Pattern) (ha : d4457 q = 1) (hb : d68222 q = 1) : d68607 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4457, d68607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4457, d68607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4458 q = 1) (hb : d68222 q = 1) : d68608 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4458, d68608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4458, d68608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4459 q = 1) (hb : d68222 q = 1) : d68609 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4459, d68609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4459, d68609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4461 q = 1) (hb : d68222 q = 1) : d67734 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4461, d67734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4461, d67734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4041 q ha hb
  have h6 (q : Pattern) (ha : d4462 q = 1) (hb : d68222 q = 1) : d68610 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4462, d68610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4462, d68610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d4463 q = 1) (hb : d68222 q = 1) : d68611 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4463, d68611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4463, d68611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d4464 q = 1) (hb : d68222 q = 1) : d68612 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4464, d68612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4464, d68612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d4465 q = 1) (hb : d68222 q = 1) : d68613 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4465, d68613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4465, d68613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4471 q = 1) (hb : d68222 q = 1) : d67743 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4471, d67743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4471, d67743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4042 q ha hb
  have h11 (q : Pattern) (ha : d4472 q = 1) (hb : d68222 q = 1) : d68614 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4472, d68614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4472, d68614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4473 q = 1) (hb : d68222 q = 1) : d68615 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4473, d68615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4473, d68615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d4474 q = 1) (hb : d68222 q = 1) : d68616 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4474, d68616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4474, d68616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d4475 q = 1) (hb : d68222 q = 1) : d68617 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4475, d68617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4475, d68617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d4476 q = 1) (hb : d68222 q = 1) : d68618 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d4476, d68618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4476, d68618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro7254 (p : Pattern) (ha : d4482 p = 1) (hb : d68222 p = 1) : d68624 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4477 q = 1) (hb : d68222 q = 1) : d68619 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d4477, d68619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4477, d68619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7253 q ha hb
  have h2 (q : Pattern) (ha : d4478 q = 1) (hb : d68222 q = 1) : d68620 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d4478, d68620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4478, d68620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4479 q = 1) (hb : d68222 q = 1) : d68621 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d4479, d68621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4479, d68621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4480 q = 1) (hb : d68222 q = 1) : d68622 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d4480, d68622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4480, d68622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4481 q = 1) (hb : d68222 q = 1) : d68623 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d4481, d68623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4481, d68623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4482 q = 1) (hb : d68222 q = 1) : d68624 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d4482, d68624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4482, d68624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7255 (p : Pattern) (ha : d4489 p = 1) (hb : d68222 p = 1) : d68629 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4485 q = 1) (hb : d68221 q = 1) : d4485 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1321 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4486 q = 1) (hb : d68222 q = 1) : d67757 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4486, d68222, d67757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4486, d68222, d67757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4487 q = 1) (hb : d68222 q = 1) : d68627 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4487, d68627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4487, d68627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4488 q = 1) (hb : d68222 q = 1) : d68628 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4488, d68628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4488, d68628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4489 q = 1) (hb : d68222 q = 1) : d68629 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4489, d68629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4489, d68629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7256 (p : Pattern) (ha : d4494 p = 1) (hb : d68222 p = 1) : d68630 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4485 q = 1) (hb : d68221 q = 1) : d4485 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1321 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4486 q = 1) (hb : d68222 q = 1) : d67757 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4486, d68222, d67757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4486, d68222, d67757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4487 q = 1) (hb : d68222 q = 1) : d68627 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4487, d68627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4487, d68627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4488 q = 1) (hb : d68222 q = 1) : d68628 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4488, d68628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4488, d68628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4490 q = 1) (hb : d68221 q = 1) : d4490 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1344 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d4491 q = 1) (hb : d68222 q = 1) : d67761 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4491, d68222, d67761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4491, d68222, d67761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d4492 q = 1) (hb : d68222 q = 1) : d67769 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4492, d67769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4492, d67769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4493 q = 1) (hb : d68222 q = 1) : d67770 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4493, d67770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4493, d67770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4494 q = 1) (hb : d68222 q = 1) : d68630 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4494, d68630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4494, d68630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro7257 (p : Pattern) (ha : d4515 p = 1) (hb : d68222 p = 1) : d68643 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4495 q = 1) (hb : d68222 q = 1) : d68631 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4495, d68631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7255 q ha hb
    | true =>
      simp only [d4495, d68631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7256 q ha hb
  have h2 (q : Pattern) (ha : d4496 q = 1) (hb : d68222 q = 1) : d68632 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4496, d68632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4496, d68632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4497 q = 1) (hb : d68222 q = 1) : d68633 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4497, d68633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4497, d68633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4498 q = 1) (hb : d68222 q = 1) : d68634 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4498, d68634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4498, d68634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4500 q = 1) (hb : d68222 q = 1) : d67772 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4500, d67772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4500, d67772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4053 q ha hb
  have h6 (q : Pattern) (ha : d4501 q = 1) (hb : d68222 q = 1) : d68635 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4501, d68635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4501, d68635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d4502 q = 1) (hb : d68222 q = 1) : d68636 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4502, d68636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4502, d68636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d4503 q = 1) (hb : d68222 q = 1) : d68637 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4503, d68637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4503, d68637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d4504 q = 1) (hb : d68222 q = 1) : d68638 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4504, d68638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4504, d68638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4510 q = 1) (hb : d68222 q = 1) : d67781 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4510, d67781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4510, d67781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4054 q ha hb
  have h11 (q : Pattern) (ha : d4511 q = 1) (hb : d68222 q = 1) : d68639 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4511, d68639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4511, d68639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4512 q = 1) (hb : d68222 q = 1) : d68640 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4512, d68640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4512, d68640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d4513 q = 1) (hb : d68222 q = 1) : d68641 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4513, d68641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4513, d68641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d4514 q = 1) (hb : d68222 q = 1) : d68642 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4514, d68642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4514, d68642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d4515 q = 1) (hb : d68222 q = 1) : d68643 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d4515, d68643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4515, d68643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro7258 (p : Pattern) (ha : d4521 p = 1) (hb : d68222 p = 1) : d68649 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4516 q = 1) (hb : d68222 q = 1) : d68644 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d4516, d68644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4516, d68644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7257 q ha hb
  have h2 (q : Pattern) (ha : d4517 q = 1) (hb : d68222 q = 1) : d68645 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d4517, d68645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4517, d68645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4518 q = 1) (hb : d68222 q = 1) : d68646 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d4518, d68646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4518, d68646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4519 q = 1) (hb : d68222 q = 1) : d68647 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d4519, d68647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4519, d68647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4520 q = 1) (hb : d68222 q = 1) : d68648 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d4520, d68648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4520, d68648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4521 q = 1) (hb : d68222 q = 1) : d68649 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d4521, d68649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4521, d68649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7259 (p : Pattern) (ha : d4529 p = 1) (hb : d68222 p = 1) : d68655 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4525 q = 1) (hb : d68221 q = 1) : d4525 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1798 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4526 q = 1) (hb : d68222 q = 1) : d67796 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4526, d68222, d67796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4526, d68222, d67796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4527 q = 1) (hb : d68222 q = 1) : d68653 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4527, d68653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4527, d68653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4528 q = 1) (hb : d68222 q = 1) : d68654 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4528, d68654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4528, d68654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4529 q = 1) (hb : d68222 q = 1) : d68655 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4529, d68655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4529, d68655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7260 (p : Pattern) (ha : d4534 p = 1) (hb : d68222 p = 1) : d68656 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4525 q = 1) (hb : d68221 q = 1) : d4525 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1798 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4526 q = 1) (hb : d68222 q = 1) : d67796 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4526, d68222, d67796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4526, d68222, d67796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4527 q = 1) (hb : d68222 q = 1) : d68653 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4527, d68653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4527, d68653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4528 q = 1) (hb : d68222 q = 1) : d68654 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4528, d68654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4528, d68654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4530 q = 1) (hb : d68221 q = 1) : d4530 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1821 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d4531 q = 1) (hb : d68222 q = 1) : d67800 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4531, d68222, d67800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4531, d68222, d67800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d4532 q = 1) (hb : d68222 q = 1) : d67808 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4532, d67808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4532, d67808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4533 q = 1) (hb : d68222 q = 1) : d67809 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4533, d67809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4533, d67809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4534 q = 1) (hb : d68222 q = 1) : d68656 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4534, d68656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4534, d68656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro7261 (p : Pattern) (ha : d4555 p = 1) (hb : d68222 p = 1) : d68669 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4535 q = 1) (hb : d68222 q = 1) : d68657 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4535, d68657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7259 q ha hb
    | true =>
      simp only [d4535, d68657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7260 q ha hb
  have h2 (q : Pattern) (ha : d4536 q = 1) (hb : d68222 q = 1) : d68658 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4536, d68658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4536, d68658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4537 q = 1) (hb : d68222 q = 1) : d68659 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4537, d68659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4537, d68659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4538 q = 1) (hb : d68222 q = 1) : d68660 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4538, d68660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4538, d68660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4540 q = 1) (hb : d68222 q = 1) : d67811 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4540, d67811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4540, d67811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4065 q ha hb
  have h6 (q : Pattern) (ha : d4541 q = 1) (hb : d68222 q = 1) : d68661 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4541, d68661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4541, d68661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d4542 q = 1) (hb : d68222 q = 1) : d68662 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4542, d68662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4542, d68662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d4543 q = 1) (hb : d68222 q = 1) : d68663 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4543, d68663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4543, d68663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d4544 q = 1) (hb : d68222 q = 1) : d68664 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4544, d68664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4544, d68664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4550 q = 1) (hb : d68222 q = 1) : d67820 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4550, d67820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4550, d67820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4066 q ha hb
  have h11 (q : Pattern) (ha : d4551 q = 1) (hb : d68222 q = 1) : d68665 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4551, d68665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4551, d68665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4552 q = 1) (hb : d68222 q = 1) : d68666 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4552, d68666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4552, d68666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d4553 q = 1) (hb : d68222 q = 1) : d68667 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4553, d68667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4553, d68667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d4554 q = 1) (hb : d68222 q = 1) : d68668 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4554, d68668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4554, d68668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d4555 q = 1) (hb : d68222 q = 1) : d68669 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d4555, d68669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4555, d68669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro7262 (p : Pattern) (ha : d4561 p = 1) (hb : d68222 p = 1) : d68675 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4556 q = 1) (hb : d68222 q = 1) : d68670 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d4556, d68670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4556, d68670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7261 q ha hb
  have h2 (q : Pattern) (ha : d4557 q = 1) (hb : d68222 q = 1) : d68671 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d4557, d68671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4557, d68671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4558 q = 1) (hb : d68222 q = 1) : d68672 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d4558, d68672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4558, d68672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4559 q = 1) (hb : d68222 q = 1) : d68673 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d4559, d68673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4559, d68673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4560 q = 1) (hb : d68222 q = 1) : d68674 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d4560, d68674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4560, d68674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4561 q = 1) (hb : d68222 q = 1) : d68675 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d4561, d68675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4561, d68675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7263 (p : Pattern) (ha : d4570 p = 1) (hb : d68222 p = 1) : d68682 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4566 q = 1) (hb : d68221 q = 1) : d4566 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2276 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4567 q = 1) (hb : d68222 q = 1) : d67836 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4567, d68222, d67836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4567, d68222, d67836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4568 q = 1) (hb : d68222 q = 1) : d68680 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4568, d68680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4568, d68680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4569 q = 1) (hb : d68222 q = 1) : d68681 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4569, d68681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4569, d68681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4570 q = 1) (hb : d68222 q = 1) : d68682 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4570, d68682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4570, d68682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7264 (p : Pattern) (ha : d4575 p = 1) (hb : d68222 p = 1) : d68683 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4566 q = 1) (hb : d68221 q = 1) : d4566 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2276 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4567 q = 1) (hb : d68222 q = 1) : d67836 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4567, d68222, d67836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4567, d68222, d67836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4568 q = 1) (hb : d68222 q = 1) : d68680 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4568, d68680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4568, d68680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4569 q = 1) (hb : d68222 q = 1) : d68681 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4569, d68681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4569, d68681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4571 q = 1) (hb : d68221 q = 1) : d4571 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d2299 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d4572 q = 1) (hb : d68222 q = 1) : d67840 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4572, d68222, d67840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4572, d68222, d67840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d4573 q = 1) (hb : d68222 q = 1) : d67848 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4573, d67848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4573, d67848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4574 q = 1) (hb : d68222 q = 1) : d67849 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4574, d67849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4574, d67849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4575 q = 1) (hb : d68222 q = 1) : d68683 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4575, d68683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4575, d68683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro7265 (p : Pattern) (ha : d4596 p = 1) (hb : d68222 p = 1) : d68696 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4576 q = 1) (hb : d68222 q = 1) : d68684 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4576, d68684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7263 q ha hb
    | true =>
      simp only [d4576, d68684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7264 q ha hb
  have h2 (q : Pattern) (ha : d4577 q = 1) (hb : d68222 q = 1) : d68685 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4577, d68685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4577, d68685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4578 q = 1) (hb : d68222 q = 1) : d68686 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4578, d68686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4578, d68686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4579 q = 1) (hb : d68222 q = 1) : d68687 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4579, d68687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4579, d68687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4581 q = 1) (hb : d68222 q = 1) : d67851 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4581, d67851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4581, d67851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4077 q ha hb
  have h6 (q : Pattern) (ha : d4582 q = 1) (hb : d68222 q = 1) : d68688 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4582, d68688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4582, d68688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d4583 q = 1) (hb : d68222 q = 1) : d68689 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4583, d68689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4583, d68689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d4584 q = 1) (hb : d68222 q = 1) : d68690 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4584, d68690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4584, d68690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d4585 q = 1) (hb : d68222 q = 1) : d68691 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4585, d68691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4585, d68691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4591 q = 1) (hb : d68222 q = 1) : d67860 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4591, d67860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4591, d67860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4078 q ha hb
  have h11 (q : Pattern) (ha : d4592 q = 1) (hb : d68222 q = 1) : d68692 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4592, d68692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4592, d68692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4593 q = 1) (hb : d68222 q = 1) : d68693 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4593, d68693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4593, d68693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d4594 q = 1) (hb : d68222 q = 1) : d68694 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4594, d68694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4594, d68694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d4595 q = 1) (hb : d68222 q = 1) : d68695 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4595, d68695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4595, d68695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d4596 q = 1) (hb : d68222 q = 1) : d68696 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d4596, d68696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4596, d68696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro7266 (p : Pattern) (ha : d4602 p = 1) (hb : d68222 p = 1) : d68702 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4597 q = 1) (hb : d68222 q = 1) : d68697 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d4597, d68697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4597, d68697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7265 q ha hb
  have h2 (q : Pattern) (ha : d4598 q = 1) (hb : d68222 q = 1) : d68698 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d4598, d68698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4598, d68698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4599 q = 1) (hb : d68222 q = 1) : d68699 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d4599, d68699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4599, d68699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4600 q = 1) (hb : d68222 q = 1) : d68700 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d4600, d68700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4600, d68700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4601 q = 1) (hb : d68222 q = 1) : d68701 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d4601, d68701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4601, d68701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4602 q = 1) (hb : d68222 q = 1) : d68702 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d4602, d68702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4602, d68702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7267 (p : Pattern) (ha : d4608 p = 1) (hb : d68222 p = 1) : d68708 p = 1 := by
  have h0 (q : Pattern) (ha : d4445 q = 1) (hb : d68222 q = 1) : d68601 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d4445, d68601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7246 q ha hb
    | true =>
      simp only [d4445, d68601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7250 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4483 q = 1) (hb : d68222 q = 1) : d68625 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d4483, d68625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4483, d68625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7254 q ha hb
  have h3 (q : Pattern) (ha : d4484 q = 1) (hb : d68222 q = 1) : d68626 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d4484, d68626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4484, d68626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4522 q = 1) (hb : d68222 q = 1) : d68650 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d4522, d68650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4522, d68650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7258 q ha hb
  have h5 (q : Pattern) (ha : d4523 q = 1) (hb : d68222 q = 1) : d68651 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d4523, d68651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4523, d68651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4524 q = 1) (hb : d68222 q = 1) : d68652 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d4524, d68652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4524, d68652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4562 q = 1) (hb : d68222 q = 1) : d68676 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d4562, d68676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4562, d68676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7262 q ha hb
  have h8 (q : Pattern) (ha : d4563 q = 1) (hb : d68222 q = 1) : d68677 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d4563, d68677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4563, d68677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4564 q = 1) (hb : d68222 q = 1) : d68678 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d4564, d68678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4564, d68678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4565 q = 1) (hb : d68222 q = 1) : d68679 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d4565, d68679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4565, d68679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4603 q = 1) (hb : d68222 q = 1) : d68703 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d4603, d68703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4603, d68703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7266 q ha hb
  have h12 (q : Pattern) (ha : d4604 q = 1) (hb : d68222 q = 1) : d68704 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d4604, d68704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4604, d68704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d4605 q = 1) (hb : d68222 q = 1) : d68705 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d4605, d68705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4605, d68705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d4606 q = 1) (hb : d68222 q = 1) : d68706 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d4606, d68706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4606, d68706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d4607 q = 1) (hb : d68222 q = 1) : d68707 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d4607, d68707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4607, d68707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d4608 q = 1) (hb : d68222 q = 1) : d68708 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d4608, d68708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d4608, d68708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro7268 (p : Pattern) (ha : d4614 p = 1) (hb : d68222 p = 1) : d68714 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4609 q = 1) (hb : d68222 q = 1) : d68709 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d4609, d68709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7267 q ha hb
    | true =>
      simp only [d4609, d68709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4610 q = 1) (hb : d68222 q = 1) : d68710 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d4610, d68710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4610, d68710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4611 q = 1) (hb : d68222 q = 1) : d68711 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d4611, d68711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4611, d68711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4612 q = 1) (hb : d68222 q = 1) : d68712 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d4612, d68712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4612, d68712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4613 q = 1) (hb : d68222 q = 1) : d68713 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d4613, d68713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4613, d68713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4614 q = 1) (hb : d68222 q = 1) : d68714 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d4614, d68714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4614, d68714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7269 (p : Pattern) (ha : d4620 p = 1) (hb : d68222 p = 1) : d68720 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4615 q = 1) (hb : d68222 q = 1) : d68715 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d4615, d68715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7268 q ha hb
    | true =>
      simp only [d4615, d68715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4616 q = 1) (hb : d68222 q = 1) : d68716 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d4616, d68716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4616, d68716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4617 q = 1) (hb : d68222 q = 1) : d68717 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d4617, d68717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4617, d68717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4618 q = 1) (hb : d68222 q = 1) : d68718 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d4618, d68718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4618, d68718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4619 q = 1) (hb : d68222 q = 1) : d68719 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d4619, d68719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4619, d68719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4620 q = 1) (hb : d68222 q = 1) : d68720 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d4620, d68720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4620, d68720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7270 (p : Pattern) (ha : d4626 p = 1) (hb : d68222 p = 1) : d68726 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4621 q = 1) (hb : d68222 q = 1) : d68721 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d4621, d68721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7269 q ha hb
    | true =>
      simp only [d4621, d68721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4622 q = 1) (hb : d68222 q = 1) : d68722 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d4622, d68722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4622, d68722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4623 q = 1) (hb : d68222 q = 1) : d68723 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d4623, d68723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4623, d68723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4624 q = 1) (hb : d68222 q = 1) : d68724 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d4624, d68724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4624, d68724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4625 q = 1) (hb : d68222 q = 1) : d68725 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d4625, d68725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4625, d68725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4626 q = 1) (hb : d68222 q = 1) : d68726 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d4626, d68726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4626, d68726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7271 (p : Pattern) (ha : d4632 p = 1) (hb : d68222 p = 1) : d68732 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4627 q = 1) (hb : d68222 q = 1) : d68727 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d4627, d68727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7270 q ha hb
    | true =>
      simp only [d4627, d68727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4628 q = 1) (hb : d68222 q = 1) : d68728 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d4628, d68728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4628, d68728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4629 q = 1) (hb : d68222 q = 1) : d68729 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d4629, d68729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4629, d68729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4630 q = 1) (hb : d68222 q = 1) : d68730 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d4630, d68730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4630, d68730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4631 q = 1) (hb : d68222 q = 1) : d68731 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d4631, d68731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4631, d68731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4632 q = 1) (hb : d68222 q = 1) : d68732 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d4632, d68732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4632, d68732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7272 (p : Pattern) (ha : d4638 p = 1) (hb : d68222 p = 1) : d68738 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4633 q = 1) (hb : d68222 q = 1) : d68733 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d4633, d68733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7271 q ha hb
    | true =>
      simp only [d4633, d68733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4634 q = 1) (hb : d68222 q = 1) : d68734 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d4634, d68734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4634, d68734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4635 q = 1) (hb : d68222 q = 1) : d68735 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d4635, d68735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4635, d68735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4636 q = 1) (hb : d68222 q = 1) : d68736 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d4636, d68736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4636, d68736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4637 q = 1) (hb : d68222 q = 1) : d68737 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d4637, d68737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4637, d68737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4638 q = 1) (hb : d68222 q = 1) : d68738 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d4638, d68738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4638, d68738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7273 (p : Pattern) (ha : d4644 p = 1) (hb : d68222 p = 1) : d68744 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4639 q = 1) (hb : d68222 q = 1) : d68739 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d4639, d68739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7272 q ha hb
    | true =>
      simp only [d4639, d68739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4640 q = 1) (hb : d68222 q = 1) : d68740 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d4640, d68740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4640, d68740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4641 q = 1) (hb : d68222 q = 1) : d68741 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d4641, d68741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4641, d68741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4642 q = 1) (hb : d68222 q = 1) : d68742 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d4642, d68742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4642, d68742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4643 q = 1) (hb : d68222 q = 1) : d68743 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d4643, d68743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4643, d68743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4644 q = 1) (hb : d68222 q = 1) : d68744 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d4644, d68744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4644, d68744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7274 (p : Pattern) (ha : d4650 p = 1) (hb : d68222 p = 1) : d68750 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4645 q = 1) (hb : d68222 q = 1) : d68745 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d4645, d68745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7273 q ha hb
    | true =>
      simp only [d4645, d68745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4646 q = 1) (hb : d68222 q = 1) : d68746 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d4646, d68746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4646, d68746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4647 q = 1) (hb : d68222 q = 1) : d68747 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d4647, d68747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4647, d68747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4648 q = 1) (hb : d68222 q = 1) : d68748 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d4648, d68748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4648, d68748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4649 q = 1) (hb : d68222 q = 1) : d68749 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d4649, d68749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4649, d68749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4650 q = 1) (hb : d68222 q = 1) : d68750 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d4650, d68750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4650, d68750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7275 (p : Pattern) (ha : d67305 p = 1) (hb : d68542 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d157 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30 q ha hb
    | true =>
      simp only [d157, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4335 q = 1) (hb : d52009 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d52009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4335, d52009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67302 q = 1) (hb : d67611 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67302, d67611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d67302, d67611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d67303 q = 1) (hb : d68540 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67303, d68540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d67303, d68540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d67304 q = 1) (hb : d68541 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67304, d68541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d67304, d68541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d67305 q = 1) (hb : d68542 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67305, d68542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67305, d68542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro7276 (p : Pattern) (ha : d67309 p = 1) (hb : d68543 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d157 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30 q ha hb
    | true =>
      simp only [d157, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4335 q = 1) (hb : d52009 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d52009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4335, d52009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d67302 q = 1) (hb : d67611 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67302, d67611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d67302, d67611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d67303 q = 1) (hb : d68540 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67303, d68540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d67303, d68540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d67304 q = 1) (hb : d68541 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67304, d68541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67304, d68541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52018 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52022 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d204 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22 q ha hb
    | true =>
      simp only [d204, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4340 q = 1) (hb : d52025 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d52025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4340, d52025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d67306 q = 1) (hb : d67615 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67306, d67615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d67306, d67615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h15 (q : Pattern) (ha : d67307 q = 1) (hb : d67623 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67307, d67623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d67307, d67623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d67308 q = 1) (hb : d67624 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67308, d67624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d67308, d67624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d67309 q = 1) (hb : d68543 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67309, d68543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d67309, d68543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro7277 (p : Pattern) (ha : d67331 p = 1) (hb : d68549 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51966 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d67310 q = 1) (hb : d68544 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67310, d68544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7275 q ha hb
    | true =>
      simp only [d67310, d68544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7276 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52032 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d67311 q = 1) (hb : d68545 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67311, d68545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67311, d68545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d67312 q = 1) (hb : d68546 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67312, d68546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67312, d68546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d67313 q = 1) (hb : d68547 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67313, d68547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67313, d68547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d67317 q = 1) (hb : d67626 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67317, d67626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d67317, d67626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3732 q ha hb
  have h8 (q : Pattern) (ha : d67318 q = 1) (hb : d67627 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67318, d67627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d67318, d67627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d67319 q = 1) (hb : d67628 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67319, d67628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d67319, d67628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d67320 q = 1) (hb : d67629 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67320, d67629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d67320, d67629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d67321 q = 1) (hb : d68548 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d67321, d68548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d67321, d68548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d67326 q = 1) (hb : d67635 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67326, d67635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d67326, d67635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3733 q ha hb
  have h13 (q : Pattern) (ha : d67327 q = 1) (hb : d67636 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67327, d67636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d67327, d67636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d67328 q = 1) (hb : d67637 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67328, d67637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d67328, d67637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d67329 q = 1) (hb : d67638 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67329, d67638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d67329, d67638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h16 (q : Pattern) (ha : d67330 q = 1) (hb : d67639 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d67330, d67639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d67330, d67639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d67331 q = 1) (hb : d68549 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d67331, d68549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d67331, d68549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro7278 (p : Pattern) (ha : d67340 p = 1) (hb : d68557 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52099 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52105 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d337 q = 1) (hb : d52136 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d337, d52136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53 q ha hb
    | true =>
      simp only [d337, d52136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4371 q = 1) (hb : d52137 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4371, d52137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4371, d52137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67337 q = 1) (hb : d67646 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67337, d67646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d67337, d67646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d67338 q = 1) (hb : d68555 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67338, d68555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d67338, d68555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d67339 q = 1) (hb : d68556 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67339, d68556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d67339, d68556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d67340 q = 1) (hb : d68557 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67340, d68557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67340, d68557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro7279 (p : Pattern) (ha : d67344 p = 1) (hb : d68558 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52105 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d337 q = 1) (hb : d52136 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d337, d52136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53 q ha hb
    | true =>
      simp only [d337, d52136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4371 q = 1) (hb : d52137 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4371, d52137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4371, d52137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d67337 q = 1) (hb : d67646 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67337, d67646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d67337, d67646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d67338 q = 1) (hb : d68555 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67338, d68555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d67338, d68555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d67339 q = 1) (hb : d68556 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67339, d68556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67339, d68556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52148 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52152 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d386 q = 1) (hb : d52154 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d386, d52154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45 q ha hb
    | true =>
      simp only [d386, d52154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4376 q = 1) (hb : d52155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4376, d52155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4376, d52155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d67341 q = 1) (hb : d67650 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67341, d67650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d67341, d67650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h15 (q : Pattern) (ha : d67342 q = 1) (hb : d67658 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67342, d67658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d67342, d67658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d67343 q = 1) (hb : d67659 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67343, d67659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d67343, d67659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d67344 q = 1) (hb : d68558 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67344, d68558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d67344, d68558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro7280 (p : Pattern) (ha : d67366 p = 1) (hb : d68571 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52093 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d67345 q = 1) (hb : d68559 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67345, d68559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7278 q ha hb
    | true =>
      simp only [d67345, d68559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7279 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52164 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d67346 q = 1) (hb : d68560 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67346, d68560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67346, d68560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d67347 q = 1) (hb : d68561 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67347, d68561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67347, d68561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d67348 q = 1) (hb : d68562 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67348, d68562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67348, d68562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d67352 q = 1) (hb : d67661 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67352, d67661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d67352, d67661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3737 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d67353 q = 1) (hb : d68563 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67353, d68563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d67353, d68563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d67354 q = 1) (hb : d68564 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67354, d68564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d67354, d68564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d67355 q = 1) (hb : d68565 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67355, d68565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d67355, d68565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d67356 q = 1) (hb : d68566 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d67356, d68566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d67356, d68566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d67361 q = 1) (hb : d67670 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67361, d67670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d67361, d67670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3738 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d67362 q = 1) (hb : d68567 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67362, d68567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d67362, d68567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d67363 q = 1) (hb : d68568 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67363, d68568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d67363, d68568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d67364 q = 1) (hb : d68569 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67364, d68569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d67364, d68569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d67365 q = 1) (hb : d68570 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d67365, d68570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d67365, d68570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d67366 q = 1) (hb : d68571 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d67366, d68571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d67366, d68571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro7281 (p : Pattern) (ha : d67372 p = 1) (hb : d68577 p = 1) : d0 p = 1 := by
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
  have h5 (q : Pattern) (ha : d67332 q = 1) (hb : d68550 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d67332, d68550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67332, d68550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7277 q ha hb
  have h6 (q : Pattern) (ha : d67333 q = 1) (hb : d68551 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d67333, d68551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67333, d68551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d67334 q = 1) (hb : d68552 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d67334, d68552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67334, d68552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d67335 q = 1) (hb : d68553 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d67335, d68553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67335, d68553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d67336 q = 1) (hb : d68554 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d67336, d68554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d67336, d68554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d67367 q = 1) (hb : d68572 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d67367, d68572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67367, d68572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7280 q ha hb
  have h11 (q : Pattern) (ha : d67368 q = 1) (hb : d68573 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d67368, d68573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67368, d68573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d67369 q = 1) (hb : d68574 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d67369, d68574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67369, d68574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d67370 q = 1) (hb : d68575 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d67370, d68575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67370, d68575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d67371 q = 1) (hb : d68576 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d67371, d68576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67371, d68576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d67372 q = 1) (hb : d68577 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d67372, d68577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d67372, d68577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro7282 (p : Pattern) (ha : d67376 p = 1) (hb : d68580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52265 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52274 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d561 q = 1) (hb : d52308 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d561, d52308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91 q ha hb
    | true =>
      simp only [d561, d52308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52239 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4408 q = 1) (hb : d52309 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4408, d52309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4408, d52309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67373 q = 1) (hb : d67682 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67373, d67682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d67373, d67682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d67374 q = 1) (hb : d68578 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67374, d68578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d67374, d68578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d67375 q = 1) (hb : d68579 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67375, d68579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d67375, d68579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d67376 q = 1) (hb : d68580 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67376, d68580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67376, d68580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro7283 (p : Pattern) (ha : d67380 p = 1) (hb : d68581 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52265 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52274 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d561 q = 1) (hb : d52308 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d561, d52308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91 q ha hb
    | true =>
      simp only [d561, d52308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52239 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4408 q = 1) (hb : d52309 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4408, d52309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4408, d52309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d67373 q = 1) (hb : d67682 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67373, d67682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d67373, d67682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d67374 q = 1) (hb : d68578 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67374, d68578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d67374, d68578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d67375 q = 1) (hb : d68579 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67375, d68579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67375, d68579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52321 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52326 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d621 q = 1) (hb : d52328 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d621, d52328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79 q ha hb
    | true =>
      simp only [d621, d52328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d52249 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4413 q = 1) (hb : d52329 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4413, d52329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4413, d52329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d67377 q = 1) (hb : d67686 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67377, d67686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d67377, d67686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h15 (q : Pattern) (ha : d67378 q = 1) (hb : d67694 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67378, d67694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d67378, d67694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d67379 q = 1) (hb : d67695 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67379, d67695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d67379, d67695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d67380 q = 1) (hb : d68581 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67380, d68581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d67380, d68581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro7284 (p : Pattern) (ha : d67402 p = 1) (hb : d68594 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52257 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d67381 q = 1) (hb : d68582 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67381, d68582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7282 q ha hb
    | true =>
      simp only [d67381, d68582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7283 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52349 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d67382 q = 1) (hb : d68583 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67382, d68583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67382, d68583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d67383 q = 1) (hb : d68584 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67383, d68584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67383, d68584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d67384 q = 1) (hb : d68585 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67384, d68585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67384, d68585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d67388 q = 1) (hb : d67697 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67388, d67697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d67388, d67697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3743 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52358 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d67389 q = 1) (hb : d68586 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67389, d68586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d67389, d68586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d67390 q = 1) (hb : d68587 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67390, d68587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d67390, d68587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d67391 q = 1) (hb : d68588 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67391, d68588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d67391, d68588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d67392 q = 1) (hb : d68589 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d67392, d68589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d67392, d68589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d67397 q = 1) (hb : d67706 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67397, d67706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d67397, d67706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3744 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52414 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d67398 q = 1) (hb : d68590 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67398, d68590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d67398, d68590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d67399 q = 1) (hb : d68591 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67399, d68591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d67399, d68591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d67400 q = 1) (hb : d68592 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67400, d68592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d67400, d68592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d67401 q = 1) (hb : d68593 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d67401, d68593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d67401, d68593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d67402 q = 1) (hb : d68594 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d67402, d68594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d67402, d68594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro7285 (p : Pattern) (ha : d67408 p = 1) (hb : d68600 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d67403 q = 1) (hb : d68595 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d67403, d68595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67403, d68595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7284 q ha hb
  have h2 (q : Pattern) (ha : d67404 q = 1) (hb : d68596 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d67404, d68596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67404, d68596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d67405 q = 1) (hb : d68597 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d67405, d68597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67405, d68597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d67406 q = 1) (hb : d68598 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d67406, d68598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67406, d68598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d67407 q = 1) (hb : d68599 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d67407, d68599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67407, d68599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67408 q = 1) (hb : d68600 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d67408, d68600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67408, d68600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7286 (p : Pattern) (ha : d67413 p = 1) (hb : d68604 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52487 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52496 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d852 q = 1) (hb : d52529 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d852, d52529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro138 q ha hb
    | true =>
      simp only [d852, d52529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52461 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4446 q = 1) (hb : d52530 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4446, d52530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4446, d52530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67410 q = 1) (hb : d67719 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67410, d67719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d67410, d67719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d67411 q = 1) (hb : d68602 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67411, d68602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d67411, d68602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d67412 q = 1) (hb : d68603 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67412, d68603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d67412, d68603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d67413 q = 1) (hb : d68604 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67413, d68604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67413, d68604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro7287 (p : Pattern) (ha : d67417 p = 1) (hb : d68605 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52496 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d852 q = 1) (hb : d52529 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d852, d52529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro138 q ha hb
    | true =>
      simp only [d852, d52529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52461 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4446 q = 1) (hb : d52530 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4446, d52530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4446, d52530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d67410 q = 1) (hb : d67719 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67410, d67719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d67410, d67719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d67411 q = 1) (hb : d68602 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67411, d68602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d67411, d68602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d67412 q = 1) (hb : d68603 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67412, d68603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67412, d68603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52542 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52547 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d927 q = 1) (hb : d52549 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d927, d52549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro125 q ha hb
    | true =>
      simp only [d927, d52549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro109 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d52471 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4451 q = 1) (hb : d52550 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4451, d52550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4451, d52550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d67414 q = 1) (hb : d67723 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67414, d67723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d67414, d67723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h15 (q : Pattern) (ha : d67415 q = 1) (hb : d67731 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67415, d67731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d67415, d67731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d67416 q = 1) (hb : d67732 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67416, d67732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d67416, d67732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d67417 q = 1) (hb : d68605 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67417, d68605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d67417, d68605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro7288 (p : Pattern) (ha : d67439 p = 1) (hb : d68618 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52479 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d67418 q = 1) (hb : d68606 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67418, d68606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7286 q ha hb
    | true =>
      simp only [d67418, d68606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7287 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52570 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d67419 q = 1) (hb : d68607 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67419, d68607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67419, d68607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d67420 q = 1) (hb : d68608 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67420, d68608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67420, d68608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d67421 q = 1) (hb : d68609 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67421, d68609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67421, d68609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d67425 q = 1) (hb : d67734 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67425, d67734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d67425, d67734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3749 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52579 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d67426 q = 1) (hb : d68610 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67426, d68610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d67426, d68610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d67427 q = 1) (hb : d68611 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67427, d68611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d67427, d68611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d67428 q = 1) (hb : d68612 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67428, d68612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d67428, d68612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d67429 q = 1) (hb : d68613 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d67429, d68613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d67429, d68613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d67434 q = 1) (hb : d67743 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67434, d67743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d67434, d67743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3750 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52651 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d67435 q = 1) (hb : d68614 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67435, d68614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d67435, d68614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d67436 q = 1) (hb : d68615 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67436, d68615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d67436, d68615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d67437 q = 1) (hb : d68616 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67437, d68616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d67437, d68616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d67438 q = 1) (hb : d68617 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d67438, d68617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d67438, d68617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d67439 q = 1) (hb : d68618 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d67439, d68618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d67439, d68618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro7289 (p : Pattern) (ha : d67445 p = 1) (hb : d68624 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d67440 q = 1) (hb : d68619 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d67440, d68619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67440, d68619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7288 q ha hb
  have h2 (q : Pattern) (ha : d67441 q = 1) (hb : d68620 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d67441, d68620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67441, d68620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d67442 q = 1) (hb : d68621 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d67442, d68621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67442, d68621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d67443 q = 1) (hb : d68622 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d67443, d68622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67443, d68622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d67444 q = 1) (hb : d68623 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d67444, d68623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67444, d68623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67445 q = 1) (hb : d68624 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d67445, d68624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67445, d68624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7290 (p : Pattern) (ha : d67451 p = 1) (hb : d68629 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52770 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52779 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1228 q = 1) (hb : d52809 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1228, d52809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro190 q ha hb
    | true =>
      simp only [d1228, d52809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro158 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52744 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4485 q = 1) (hb : d52810 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4485, d52810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4485, d52810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67448 q = 1) (hb : d67757 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67448, d67757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d67448, d67757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d67449 q = 1) (hb : d68627 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67449, d68627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d67449, d68627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d67450 q = 1) (hb : d68628 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67450, d68628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d67450, d68628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d67451 q = 1) (hb : d68629 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67451, d68629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67451, d68629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro7291 (p : Pattern) (ha : d67455 p = 1) (hb : d68630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52770 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52779 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1228 q = 1) (hb : d52809 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1228, d52809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro190 q ha hb
    | true =>
      simp only [d1228, d52809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro158 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52744 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4485 q = 1) (hb : d52810 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4485, d52810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4485, d52810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d67448 q = 1) (hb : d67757 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67448, d67757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d67448, d67757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d67449 q = 1) (hb : d68627 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67449, d68627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d67449, d68627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d67450 q = 1) (hb : d68628 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67450, d68628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67450, d68628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52822 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52827 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d1338 q = 1) (hb : d52829 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1338, d52829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro177 q ha hb
    | true =>
      simp only [d1338, d52829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro161 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d52754 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4490 q = 1) (hb : d52830 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4490, d52830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4490, d52830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d67452 q = 1) (hb : d67761 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67452, d67761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d67452, d67761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h15 (q : Pattern) (ha : d67453 q = 1) (hb : d67769 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67453, d67769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d67453, d67769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d67454 q = 1) (hb : d67770 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67454, d67770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d67454, d67770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d67455 q = 1) (hb : d68630 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67455, d68630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d67455, d68630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro7292 (p : Pattern) (ha : d67477 p = 1) (hb : d68643 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d67456 q = 1) (hb : d68631 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67456, d68631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7290 q ha hb
    | true =>
      simp only [d67456, d68631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7291 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52850 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d67457 q = 1) (hb : d68632 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67457, d68632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67457, d68632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d67458 q = 1) (hb : d68633 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67458, d68633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67458, d68633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d67459 q = 1) (hb : d68634 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67459, d68634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67459, d68634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d67463 q = 1) (hb : d67772 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67463, d67772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d67463, d67772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3755 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52859 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d67464 q = 1) (hb : d68635 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67464, d68635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d67464, d68635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d67465 q = 1) (hb : d68636 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67465, d68636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d67465, d68636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d67466 q = 1) (hb : d68637 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67466, d68637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d67466, d68637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d67467 q = 1) (hb : d68638 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d67467, d68638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d67467, d68638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d67472 q = 1) (hb : d67781 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67472, d67781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d67472, d67781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3756 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52945 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d67473 q = 1) (hb : d68639 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67473, d68639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d67473, d68639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d67474 q = 1) (hb : d68640 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67474, d68640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d67474, d68640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d67475 q = 1) (hb : d68641 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67475, d68641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d67475, d68641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d67476 q = 1) (hb : d68642 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d67476, d68642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d67476, d68642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d67477 q = 1) (hb : d68643 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d67477, d68643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d67477, d68643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro7293 (p : Pattern) (ha : d67483 p = 1) (hb : d68649 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d67478 q = 1) (hb : d68644 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d67478, d68644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67478, d68644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7292 q ha hb
  have h2 (q : Pattern) (ha : d67479 q = 1) (hb : d68645 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d67479, d68645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67479, d68645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d67480 q = 1) (hb : d68646 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d67480, d68646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67480, d68646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d67481 q = 1) (hb : d68647 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d67481, d68647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67481, d68647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d67482 q = 1) (hb : d68648 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d67482, d68648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67482, d68648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67483 q = 1) (hb : d68649 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d67483, d68649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67483, d68649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7294 (p : Pattern) (ha : d67490 p = 1) (hb : d68655 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53091 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53100 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1683 q = 1) (hb : d53124 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1683, d53124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro246 q ha hb
    | true =>
      simp only [d1683, d53124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro216 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53065 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4525 q = 1) (hb : d53125 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4525, d53125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4525, d53125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67487 q = 1) (hb : d67796 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67487, d67796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d67487, d67796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d67488 q = 1) (hb : d68653 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67488, d68653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d67488, d68653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d67489 q = 1) (hb : d68654 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67489, d68654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d67489, d68654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d67490 q = 1) (hb : d68655 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67490, d68655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67490, d68655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro7295 (p : Pattern) (ha : d67494 p = 1) (hb : d68656 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53091 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53100 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1683 q = 1) (hb : d53124 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1683, d53124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro246 q ha hb
    | true =>
      simp only [d1683, d53124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro216 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53065 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4525 q = 1) (hb : d53125 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4525, d53125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4525, d53125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d67487 q = 1) (hb : d67796 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67487, d67796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d67487, d67796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d67488 q = 1) (hb : d68653 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67488, d68653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d67488, d68653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d67489 q = 1) (hb : d68654 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67489, d68654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67489, d68654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53137 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53142 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d1815 q = 1) (hb : d53144 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1815, d53144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro233 q ha hb
    | true =>
      simp only [d1815, d53144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro219 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d53075 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4530 q = 1) (hb : d53145 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4530, d53145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4530, d53145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d67491 q = 1) (hb : d67800 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67491, d67800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d67491, d67800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h15 (q : Pattern) (ha : d67492 q = 1) (hb : d67808 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67492, d67808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d67492, d67808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d67493 q = 1) (hb : d67809 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67493, d67809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d67493, d67809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d67494 q = 1) (hb : d68656 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67494, d68656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d67494, d68656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro7296 (p : Pattern) (ha : d67516 p = 1) (hb : d68669 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53083 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d67495 q = 1) (hb : d68657 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67495, d68657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7294 q ha hb
    | true =>
      simp only [d67495, d68657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7295 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53165 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d67496 q = 1) (hb : d68658 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67496, d68658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67496, d68658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d67497 q = 1) (hb : d68659 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67497, d68659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67497, d68659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d67498 q = 1) (hb : d68660 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67498, d68660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67498, d68660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d67502 q = 1) (hb : d67811 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67502, d67811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d67502, d67811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3761 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53174 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d67503 q = 1) (hb : d68661 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67503, d68661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d67503, d68661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d67504 q = 1) (hb : d68662 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67504, d68662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d67504, d68662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d67505 q = 1) (hb : d68663 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67505, d68663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d67505, d68663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d67506 q = 1) (hb : d68664 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d67506, d68664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d67506, d68664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d67511 q = 1) (hb : d67820 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67511, d67820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d67511, d67820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3762 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53260 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d67512 q = 1) (hb : d68665 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67512, d68665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d67512, d68665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d67513 q = 1) (hb : d68666 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67513, d68666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d67513, d68666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d67514 q = 1) (hb : d68667 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67514, d68667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d67514, d68667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d67515 q = 1) (hb : d68668 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d67515, d68668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d67515, d68668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d67516 q = 1) (hb : d68669 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d67516, d68669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d67516, d68669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro7297 (p : Pattern) (ha : d67522 p = 1) (hb : d68675 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d67517 q = 1) (hb : d68670 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d67517, d68670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67517, d68670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7296 q ha hb
  have h2 (q : Pattern) (ha : d67518 q = 1) (hb : d68671 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d67518, d68671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67518, d68671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d67519 q = 1) (hb : d68672 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d67519, d68672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67519, d68672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d67520 q = 1) (hb : d68673 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d67520, d68673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67520, d68673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d67521 q = 1) (hb : d68674 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d67521, d68674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67521, d68674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67522 q = 1) (hb : d68675 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d67522, d68675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67522, d68675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7298 (p : Pattern) (ha : d67530 p = 1) (hb : d68682 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53412 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53421 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2162 q = 1) (hb : d53441 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2162, d53441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro305 q ha hb
    | true =>
      simp only [d2162, d53441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro275 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4566 q = 1) (hb : d53442 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4566, d53442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4566, d53442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67527 q = 1) (hb : d67836 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67527, d67836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d67527, d67836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d67528 q = 1) (hb : d68680 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67528, d68680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d67528, d68680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d67529 q = 1) (hb : d68681 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67529, d68681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d67529, d68681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d67530 q = 1) (hb : d68682 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67530, d68682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67530, d68682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro7299 (p : Pattern) (ha : d67534 p = 1) (hb : d68683 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53412 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53421 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2162 q = 1) (hb : d53441 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2162, d53441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro305 q ha hb
    | true =>
      simp only [d2162, d53441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro275 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4566 q = 1) (hb : d53442 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4566, d53442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4566, d53442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d67527 q = 1) (hb : d67836 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67527, d67836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d67527, d67836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d67528 q = 1) (hb : d68680 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67528, d68680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d67528, d68680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d67529 q = 1) (hb : d68681 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67529, d68681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67529, d68681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53454 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53459 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d2293 q = 1) (hb : d53461 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2293, d53461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro292 q ha hb
    | true =>
      simp only [d2293, d53461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro278 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d53396 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4571 q = 1) (hb : d53462 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4571, d53462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4571, d53462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d67531 q = 1) (hb : d67840 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67531, d67840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d67531, d67840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h15 (q : Pattern) (ha : d67532 q = 1) (hb : d67848 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67532, d67848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d67532, d67848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d67533 q = 1) (hb : d67849 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67533, d67849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d67533, d67849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d67534 q = 1) (hb : d68683 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67534, d68683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d67534, d68683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro7300 (p : Pattern) (ha : d67556 p = 1) (hb : d68696 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53404 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d67535 q = 1) (hb : d68684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67535, d68684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7298 q ha hb
    | true =>
      simp only [d67535, d68684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7299 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53482 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d67536 q = 1) (hb : d68685 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67536, d68685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67536, d68685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d67537 q = 1) (hb : d68686 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67537, d68686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67537, d68686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d67538 q = 1) (hb : d68687 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67538, d68687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67538, d68687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d67542 q = 1) (hb : d67851 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67542, d67851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d67542, d67851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3767 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53491 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d67543 q = 1) (hb : d68688 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67543, d68688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d67543, d68688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d67544 q = 1) (hb : d68689 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67544, d68689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d67544, d68689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d67545 q = 1) (hb : d68690 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67545, d68690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d67545, d68690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d67546 q = 1) (hb : d68691 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d67546, d68691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d67546, d68691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d67551 q = 1) (hb : d67860 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67551, d67860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d67551, d67860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3768 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53577 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d67552 q = 1) (hb : d68692 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67552, d68692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d67552, d68692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d67553 q = 1) (hb : d68693 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67553, d68693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d67553, d68693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d67554 q = 1) (hb : d68694 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67554, d68694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d67554, d68694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d67555 q = 1) (hb : d68695 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d67555, d68695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d67555, d68695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d67556 q = 1) (hb : d68696 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d67556, d68696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d67556, d68696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro7301 (p : Pattern) (ha : d67562 p = 1) (hb : d68702 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d67557 q = 1) (hb : d68697 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d67557, d68697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67557, d68697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7300 q ha hb
  have h2 (q : Pattern) (ha : d67558 q = 1) (hb : d68698 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d67558, d68698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67558, d68698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d67559 q = 1) (hb : d68699 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d67559, d68699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67559, d68699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d67560 q = 1) (hb : d68700 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d67560, d68700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67560, d68700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d67561 q = 1) (hb : d68701 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d67561, d68701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67561, d68701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67562 q = 1) (hb : d68702 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d67562, d68702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67562, d68702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7302 (p : Pattern) (ha : d67568 p = 1) (hb : d68708 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d67409 q = 1) (hb : d68601 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d67409, d68601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7281 q ha hb
    | true =>
      simp only [d67409, d68601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7285 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d67446 q = 1) (hb : d68625 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d67446, d68625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d67446, d68625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7289 q ha hb
  have h3 (q : Pattern) (ha : d67447 q = 1) (hb : d68626 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d67447, d68626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67447, d68626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d67484 q = 1) (hb : d68650 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d67484, d68650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d67484, d68650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7293 q ha hb
  have h5 (q : Pattern) (ha : d67485 q = 1) (hb : d68651 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d67485, d68651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d67485, d68651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67486 q = 1) (hb : d68652 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d67486, d68652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67486, d68652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d67523 q = 1) (hb : d68676 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d67523, d68676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d67523, d68676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7297 q ha hb
  have h8 (q : Pattern) (ha : d67524 q = 1) (hb : d68677 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d67524, d68677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d67524, d68677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d67525 q = 1) (hb : d68678 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d67525, d68678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d67525, d68678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d67526 q = 1) (hb : d68679 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d67526, d68679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d67526, d68679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d67563 q = 1) (hb : d68703 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d67563, d68703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d67563, d68703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7301 q ha hb
  have h12 (q : Pattern) (ha : d67564 q = 1) (hb : d68704 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d67564, d68704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d67564, d68704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d67565 q = 1) (hb : d68705 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d67565, d68705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d67565, d68705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d67566 q = 1) (hb : d68706 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d67566, d68706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d67566, d68706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d67567 q = 1) (hb : d68707 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d67567, d68707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d67567, d68707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d67568 q = 1) (hb : d68708 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d67568, d68708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d67568, d68708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro7303 (p : Pattern) (ha : d67574 p = 1) (hb : d68714 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d67569 q = 1) (hb : d68709 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d67569, d68709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7302 q ha hb
    | true =>
      simp only [d67569, d68709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d67570 q = 1) (hb : d68710 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d67570, d68710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67570, d68710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d67571 q = 1) (hb : d68711 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d67571, d68711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67571, d68711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d67572 q = 1) (hb : d68712 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d67572, d68712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67572, d68712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d67573 q = 1) (hb : d68713 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d67573, d68713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d67573, d68713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d67574 q = 1) (hb : d68714 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d67574, d68714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d67574, d68714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro7304 (p : Pattern) (ha : d67580 p = 1) (hb : d68720 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d67575 q = 1) (hb : d68715 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d67575, d68715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7303 q ha hb
    | true =>
      simp only [d67575, d68715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d67576 q = 1) (hb : d68716 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d67576, d68716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67576, d68716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d67577 q = 1) (hb : d68717 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d67577, d68717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67577, d68717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d67578 q = 1) (hb : d68718 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d67578, d68718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67578, d68718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d67579 q = 1) (hb : d68719 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d67579, d68719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d67579, d68719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d67580 q = 1) (hb : d68720 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d67580, d68720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d67580, d68720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro7305 (p : Pattern) (ha : d67586 p = 1) (hb : d68726 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d67581 q = 1) (hb : d68721 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d67581, d68721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7304 q ha hb
    | true =>
      simp only [d67581, d68721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d67582 q = 1) (hb : d68722 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d67582, d68722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67582, d68722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d67583 q = 1) (hb : d68723 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d67583, d68723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67583, d68723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d67584 q = 1) (hb : d68724 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d67584, d68724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67584, d68724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d67585 q = 1) (hb : d68725 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d67585, d68725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d67585, d68725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d67586 q = 1) (hb : d68726 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d67586, d68726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d67586, d68726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro7306 (p : Pattern) (ha : d67592 p = 1) (hb : d68732 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d67587 q = 1) (hb : d68727 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d67587, d68727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7305 q ha hb
    | true =>
      simp only [d67587, d68727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d67588 q = 1) (hb : d68728 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d67588, d68728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67588, d68728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d67589 q = 1) (hb : d68729 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d67589, d68729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67589, d68729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d67590 q = 1) (hb : d68730 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d67590, d68730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67590, d68730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d67591 q = 1) (hb : d68731 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d67591, d68731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d67591, d68731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d67592 q = 1) (hb : d68732 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d67592, d68732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d67592, d68732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro7307 (p : Pattern) (ha : d67598 p = 1) (hb : d68738 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d67593 q = 1) (hb : d68733 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d67593, d68733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7306 q ha hb
    | true =>
      simp only [d67593, d68733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d67594 q = 1) (hb : d68734 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d67594, d68734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67594, d68734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d67595 q = 1) (hb : d68735 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d67595, d68735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67595, d68735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d67596 q = 1) (hb : d68736 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d67596, d68736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67596, d68736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d67597 q = 1) (hb : d68737 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d67597, d68737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d67597, d68737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d67598 q = 1) (hb : d68738 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d67598, d68738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d67598, d68738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro7308 (p : Pattern) (ha : d67604 p = 1) (hb : d68744 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d67599 q = 1) (hb : d68739 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d67599, d68739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7307 q ha hb
    | true =>
      simp only [d67599, d68739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d67600 q = 1) (hb : d68740 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d67600, d68740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67600, d68740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d67601 q = 1) (hb : d68741 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d67601, d68741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67601, d68741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d67602 q = 1) (hb : d68742 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d67602, d68742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67602, d68742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d67603 q = 1) (hb : d68743 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d67603, d68743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d67603, d68743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d67604 q = 1) (hb : d68744 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d67604, d68744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d67604, d68744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro7309 (p : Pattern) (ha : d67610 p = 1) (hb : d68750 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d67605 q = 1) (hb : d68745 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d67605, d68745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7308 q ha hb
    | true =>
      simp only [d67605, d68745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d67606 q = 1) (hb : d68746 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d67606, d68746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67606, d68746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d67607 q = 1) (hb : d68747 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d67607, d68747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67607, d68747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d67608 q = 1) (hb : d68748 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d67608, d68748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67608, d68748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d67609 q = 1) (hb : d68749 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d67609, d68749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d67609, d68749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d67610 q = 1) (hb : d68750 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d67610, d68750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d67610, d68750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro7310 (p : Pattern) (ha : d0 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro7311 (p : Pattern) (ha : d0 p = 1) (hb : d67610 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d67610 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro7312 (p : Pattern) (ha : d0 p = 1) (hb : d67919 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d67919 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro7313 (p : Pattern) (ha : d4365 p = 1) (hb : d73191 p = 1) : d73201 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4345 q = 1) (hb : d73190 q = 1) : d73196 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4345, d73196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7167 q ha hb
    | true =>
      simp only [d4345, d73196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7168 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4346 q = 1) (hb : d73191 q = 1) : d73197 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4346, d73191, d73197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4346, d73191, d73197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4347 q = 1) (hb : d73191 q = 1) : d73198 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4347, d73198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4347, d73198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4348 q = 1) (hb : d73191 q = 1) : d73199 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4348, d73199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4348, d73199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4350 q = 1) (hb : d73190 q = 1) : d69448 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4350, d69448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4350, d69448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5071 q ha hb
  have h8 (q : Pattern) (ha : d4351 q = 1) (hb : d73191 q = 1) : d69449 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4351, d73191, d69449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4351, d73191, d69449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d4352 q = 1) (hb : d73191 q = 1) : d69450 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4352, d69450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4352, d69450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d4353 q = 1) (hb : d73191 q = 1) : d69451 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4353, d69451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4353, d69451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d4354 q = 1) (hb : d73191 q = 1) : d73200 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4354, d73200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4354, d73200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4360 q = 1) (hb : d73190 q = 1) : d69457 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4360, d69457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4360, d69457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5072 q ha hb
  have h13 (q : Pattern) (ha : d4361 q = 1) (hb : d73191 q = 1) : d69458 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4361, d73191, d69458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4361, d73191, d69458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d4362 q = 1) (hb : d73191 q = 1) : d69459 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4362, d69459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4362, d69459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d4363 q = 1) (hb : d73191 q = 1) : d69460 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4363, d69460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4363, d69460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d4364 q = 1) (hb : d73191 q = 1) : d69461 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4364, d69461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d4364, d69461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d4365 q = 1) (hb : d73191 q = 1) : d73201 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d4365, d73201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4365, d73201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro7314 (p : Pattern) (ha : d4401 p = 1) (hb : d73191 p = 1) : d73216 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4381 q = 1) (hb : d73190 q = 1) : d73211 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4381, d73211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7170 q ha hb
    | true =>
      simp only [d4381, d73211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7171 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4382 q = 1) (hb : d73191 q = 1) : d73212 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4382, d73191, d73212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4382, d73191, d73212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4383 q = 1) (hb : d73191 q = 1) : d73213 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4383, d73213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4383, d73213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4384 q = 1) (hb : d73191 q = 1) : d73214 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4384, d73214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4384, d73214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4386 q = 1) (hb : d73190 q = 1) : d69485 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4386, d69485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4386, d69485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5078 q ha hb
  have h8 (q : Pattern) (ha : d4387 q = 1) (hb : d73191 q = 1) : d69486 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4387, d73191, d69486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4387, d73191, d69486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d4388 q = 1) (hb : d73191 q = 1) : d69487 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4388, d69487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4388, d69487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d4389 q = 1) (hb : d73191 q = 1) : d69488 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4389, d69488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4389, d69488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d4390 q = 1) (hb : d73191 q = 1) : d73215 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4390, d73215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4390, d73215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4396 q = 1) (hb : d73190 q = 1) : d69495 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4396, d69495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4396, d69495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5079 q ha hb
  have h13 (q : Pattern) (ha : d4397 q = 1) (hb : d73191 q = 1) : d69496 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4397, d73191, d69496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4397, d73191, d69496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d4398 q = 1) (hb : d73191 q = 1) : d69497 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4398, d69497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4398, d69497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d4399 q = 1) (hb : d73191 q = 1) : d69498 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4399, d69498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4399, d69498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d4400 q = 1) (hb : d73191 q = 1) : d69499 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4400, d69499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d4400, d69499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d4401 q = 1) (hb : d73191 q = 1) : d73216 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d4401, d73216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4401, d73216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro7315 (p : Pattern) (ha : d4407 p = 1) (hb : d73191 p = 1) : d73222 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d73191 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4366 q = 1) (hb : d73191 q = 1) : d73202 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d4366, d73202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4366, d73202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7313 q ha hb
  have h3 (q : Pattern) (ha : d4367 q = 1) (hb : d73191 q = 1) : d73203 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d4367, d73203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4367, d73203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4368 q = 1) (hb : d73191 q = 1) : d73204 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d4368, d73204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4368, d73204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4369 q = 1) (hb : d73191 q = 1) : d73205 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d4369, d73205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4369, d73205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4370 q = 1) (hb : d73191 q = 1) : d73206 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d4370, d73206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4370, d73206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4402 q = 1) (hb : d73191 q = 1) : d73217 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d4402, d73217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4402, d73217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7314 q ha hb
  have h8 (q : Pattern) (ha : d4403 q = 1) (hb : d73191 q = 1) : d73218 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d4403, d73218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4403, d73218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4404 q = 1) (hb : d73191 q = 1) : d73219 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d4404, d73219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4404, d73219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4405 q = 1) (hb : d73191 q = 1) : d73220 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d4405, d73220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4405, d73220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4406 q = 1) (hb : d73191 q = 1) : d73221 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d4406, d73221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4406, d73221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4407 q = 1) (hb : d73191 q = 1) : d73222 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d4407, d73222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4407, d73222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro7316 (p : Pattern) (ha : d4438 p = 1) (hb : d73191 p = 1) : d73232 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4418 q = 1) (hb : d73190 q = 1) : d73227 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4418, d73227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7174 q ha hb
    | true =>
      simp only [d4418, d73227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7175 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4419 q = 1) (hb : d73191 q = 1) : d73228 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4419, d73191, d73228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4419, d73191, d73228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4420 q = 1) (hb : d73191 q = 1) : d73229 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4420, d73229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4420, d73229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4421 q = 1) (hb : d73191 q = 1) : d73230 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4421, d73230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4421, d73230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4423 q = 1) (hb : d73190 q = 1) : d69524 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4423, d69524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4423, d69524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5086 q ha hb
  have h8 (q : Pattern) (ha : d4424 q = 1) (hb : d73191 q = 1) : d69525 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4424, d73191, d69525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4424, d73191, d69525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d4425 q = 1) (hb : d73191 q = 1) : d69526 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4425, d69526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4425, d69526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d4426 q = 1) (hb : d73191 q = 1) : d69527 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4426, d69527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4426, d69527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d4427 q = 1) (hb : d73191 q = 1) : d73231 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4427, d73231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4427, d73231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4433 q = 1) (hb : d73190 q = 1) : d69534 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4433, d69534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4433, d69534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5087 q ha hb
  have h13 (q : Pattern) (ha : d4434 q = 1) (hb : d73191 q = 1) : d69535 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4434, d73191, d69535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4434, d73191, d69535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d4435 q = 1) (hb : d73191 q = 1) : d69536 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4435, d69536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4435, d69536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d4436 q = 1) (hb : d73191 q = 1) : d69537 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4436, d69537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4436, d69537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d4437 q = 1) (hb : d73191 q = 1) : d69538 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4437, d69538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d4437, d69538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d4438 q = 1) (hb : d73191 q = 1) : d73232 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d4438, d73232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4438, d73232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro7317 (p : Pattern) (ha : d4444 p = 1) (hb : d73191 p = 1) : d73238 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4439 q = 1) (hb : d73191 q = 1) : d73233 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d4439, d73233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4439, d73233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7316 q ha hb
  have h2 (q : Pattern) (ha : d4440 q = 1) (hb : d73191 q = 1) : d73234 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d4440, d73234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4440, d73234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4441 q = 1) (hb : d73191 q = 1) : d73235 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d4441, d73235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4441, d73235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4442 q = 1) (hb : d73191 q = 1) : d73236 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d4442, d73236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4442, d73236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4443 q = 1) (hb : d73191 q = 1) : d73237 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d4443, d73237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4443, d73237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4444 q = 1) (hb : d73191 q = 1) : d73238 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d4444, d73238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4444, d73238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7318 (p : Pattern) (ha : d4476 p = 1) (hb : d73191 p = 1) : d73249 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4456 q = 1) (hb : d73190 q = 1) : d73244 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4456, d73244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7178 q ha hb
    | true =>
      simp only [d4456, d73244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7179 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4457 q = 1) (hb : d73191 q = 1) : d73245 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4457, d73191, d73245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4457, d73191, d73245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4458 q = 1) (hb : d73191 q = 1) : d73246 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4458, d73246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4458, d73246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4459 q = 1) (hb : d73191 q = 1) : d73247 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4459, d73247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4459, d73247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4461 q = 1) (hb : d73190 q = 1) : d69564 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4461, d69564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4461, d69564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5094 q ha hb
  have h8 (q : Pattern) (ha : d4462 q = 1) (hb : d73191 q = 1) : d69565 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4462, d73191, d69565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4462, d73191, d69565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d4463 q = 1) (hb : d73191 q = 1) : d69566 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4463, d69566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4463, d69566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d4464 q = 1) (hb : d73191 q = 1) : d69567 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4464, d69567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4464, d69567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d4465 q = 1) (hb : d73191 q = 1) : d73248 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4465, d73248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4465, d73248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4471 q = 1) (hb : d73190 q = 1) : d69574 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4471, d69574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4471, d69574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5095 q ha hb
  have h13 (q : Pattern) (ha : d4472 q = 1) (hb : d73191 q = 1) : d69575 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4472, d73191, d69575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4472, d73191, d69575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d4473 q = 1) (hb : d73191 q = 1) : d69576 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4473, d69576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4473, d69576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d4474 q = 1) (hb : d73191 q = 1) : d69577 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4474, d69577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4474, d69577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d4475 q = 1) (hb : d73191 q = 1) : d69578 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4475, d69578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d4475, d69578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d4476 q = 1) (hb : d73191 q = 1) : d73249 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d4476, d73249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4476, d73249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro7319 (p : Pattern) (ha : d4482 p = 1) (hb : d73191 p = 1) : d73255 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4477 q = 1) (hb : d73191 q = 1) : d73250 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d4477, d73250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4477, d73250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7318 q ha hb
  have h2 (q : Pattern) (ha : d4478 q = 1) (hb : d73191 q = 1) : d73251 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d4478, d73251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4478, d73251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4479 q = 1) (hb : d73191 q = 1) : d73252 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d4479, d73252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4479, d73252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4480 q = 1) (hb : d73191 q = 1) : d73253 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d4480, d73253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4480, d73253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4481 q = 1) (hb : d73191 q = 1) : d73254 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d4481, d73254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4481, d73254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4482 q = 1) (hb : d73191 q = 1) : d73255 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d4482, d73255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4482, d73255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7320 (p : Pattern) (ha : d4515 p = 1) (hb : d73191 p = 1) : d73267 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4495 q = 1) (hb : d73190 q = 1) : d73262 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4495, d73262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7182 q ha hb
    | true =>
      simp only [d4495, d73262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7183 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4496 q = 1) (hb : d73191 q = 1) : d73263 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4496, d73191, d73263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4496, d73191, d73263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4497 q = 1) (hb : d73191 q = 1) : d73264 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4497, d73264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4497, d73264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4498 q = 1) (hb : d73191 q = 1) : d73265 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4498, d73265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4498, d73265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4500 q = 1) (hb : d73190 q = 1) : d69605 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4500, d69605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4500, d69605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5102 q ha hb
  have h8 (q : Pattern) (ha : d4501 q = 1) (hb : d73191 q = 1) : d69606 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4501, d73191, d69606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4501, d73191, d69606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d4502 q = 1) (hb : d73191 q = 1) : d69607 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4502, d69607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4502, d69607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d4503 q = 1) (hb : d73191 q = 1) : d69608 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4503, d69608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4503, d69608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d4504 q = 1) (hb : d73191 q = 1) : d73266 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4504, d73266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4504, d73266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4510 q = 1) (hb : d73190 q = 1) : d69615 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4510, d69615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4510, d69615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5103 q ha hb
  have h13 (q : Pattern) (ha : d4511 q = 1) (hb : d73191 q = 1) : d69616 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4511, d73191, d69616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4511, d73191, d69616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d4512 q = 1) (hb : d73191 q = 1) : d69617 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4512, d69617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4512, d69617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d4513 q = 1) (hb : d73191 q = 1) : d69618 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4513, d69618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4513, d69618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d4514 q = 1) (hb : d73191 q = 1) : d69619 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4514, d69619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d4514, d69619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d4515 q = 1) (hb : d73191 q = 1) : d73267 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d4515, d73267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4515, d73267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro7321 (p : Pattern) (ha : d4521 p = 1) (hb : d73191 p = 1) : d73273 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4516 q = 1) (hb : d73191 q = 1) : d73268 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d4516, d73268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4516, d73268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7320 q ha hb
  have h2 (q : Pattern) (ha : d4517 q = 1) (hb : d73191 q = 1) : d73269 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d4517, d73269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4517, d73269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4518 q = 1) (hb : d73191 q = 1) : d73270 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d4518, d73270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4518, d73270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4519 q = 1) (hb : d73191 q = 1) : d73271 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d4519, d73271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4519, d73271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4520 q = 1) (hb : d73191 q = 1) : d73272 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d4520, d73272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4520, d73272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4521 q = 1) (hb : d73191 q = 1) : d73273 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d4521, d73273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4521, d73273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7322 (p : Pattern) (ha : d4555 p = 1) (hb : d73191 p = 1) : d73286 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4535 q = 1) (hb : d73190 q = 1) : d73281 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4535, d73281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7186 q ha hb
    | true =>
      simp only [d4535, d73281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7187 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4536 q = 1) (hb : d73191 q = 1) : d73282 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4536, d73191, d73282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4536, d73191, d73282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4537 q = 1) (hb : d73191 q = 1) : d73283 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4537, d73283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4537, d73283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4538 q = 1) (hb : d73191 q = 1) : d73284 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4538, d73284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4538, d73284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4540 q = 1) (hb : d73190 q = 1) : d69647 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4540, d69647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4540, d69647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5110 q ha hb
  have h8 (q : Pattern) (ha : d4541 q = 1) (hb : d73191 q = 1) : d69648 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4541, d73191, d69648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4541, d73191, d69648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d4542 q = 1) (hb : d73191 q = 1) : d69649 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4542, d69649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4542, d69649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d4543 q = 1) (hb : d73191 q = 1) : d69650 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4543, d69650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4543, d69650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d4544 q = 1) (hb : d73191 q = 1) : d73285 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4544, d73285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4544, d73285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4550 q = 1) (hb : d73190 q = 1) : d69657 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4550, d69657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4550, d69657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5111 q ha hb
  have h13 (q : Pattern) (ha : d4551 q = 1) (hb : d73191 q = 1) : d69658 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4551, d73191, d69658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4551, d73191, d69658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d4552 q = 1) (hb : d73191 q = 1) : d69659 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4552, d69659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4552, d69659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d4553 q = 1) (hb : d73191 q = 1) : d69660 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4553, d69660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4553, d69660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d4554 q = 1) (hb : d73191 q = 1) : d69661 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4554, d69661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d4554, d69661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d4555 q = 1) (hb : d73191 q = 1) : d73286 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d4555, d73286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4555, d73286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro7323 (p : Pattern) (ha : d4561 p = 1) (hb : d73191 p = 1) : d73292 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4556 q = 1) (hb : d73191 q = 1) : d73287 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d4556, d73287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4556, d73287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7322 q ha hb
  have h2 (q : Pattern) (ha : d4557 q = 1) (hb : d73191 q = 1) : d73288 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d4557, d73288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4557, d73288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4558 q = 1) (hb : d73191 q = 1) : d73289 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d4558, d73289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4558, d73289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4559 q = 1) (hb : d73191 q = 1) : d73290 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d4559, d73290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4559, d73290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4560 q = 1) (hb : d73191 q = 1) : d73291 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d4560, d73291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4560, d73291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4561 q = 1) (hb : d73191 q = 1) : d73292 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d4561, d73292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4561, d73292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7324 (p : Pattern) (ha : d4596 p = 1) (hb : d73191 p = 1) : d73306 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4576 q = 1) (hb : d73190 q = 1) : d73301 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4576, d73301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7190 q ha hb
    | true =>
      simp only [d4576, d73301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7191 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4577 q = 1) (hb : d73191 q = 1) : d73302 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4577, d73191, d73302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4577, d73191, d73302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4578 q = 1) (hb : d73191 q = 1) : d73303 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4578, d73303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4578, d73303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4579 q = 1) (hb : d73191 q = 1) : d73304 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4579, d73304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4579, d73304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4581 q = 1) (hb : d73190 q = 1) : d69690 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4581, d69690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4581, d69690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5118 q ha hb
  have h8 (q : Pattern) (ha : d4582 q = 1) (hb : d73191 q = 1) : d69691 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4582, d73191, d69691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4582, d73191, d69691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d4583 q = 1) (hb : d73191 q = 1) : d69692 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4583, d69692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4583, d69692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d4584 q = 1) (hb : d73191 q = 1) : d69693 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4584, d69693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4584, d69693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d4585 q = 1) (hb : d73191 q = 1) : d73305 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4585, d73305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4585, d73305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4591 q = 1) (hb : d73190 q = 1) : d69700 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4591, d69700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4591, d69700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5119 q ha hb
  have h13 (q : Pattern) (ha : d4592 q = 1) (hb : d73191 q = 1) : d69701 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4592, d73191, d69701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4592, d73191, d69701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d4593 q = 1) (hb : d73191 q = 1) : d69702 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4593, d69702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4593, d69702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d4594 q = 1) (hb : d73191 q = 1) : d69703 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4594, d69703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4594, d69703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d4595 q = 1) (hb : d73191 q = 1) : d69704 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4595, d69704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d4595, d69704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d4596 q = 1) (hb : d73191 q = 1) : d73306 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d4596, d73306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4596, d73306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro7325 (p : Pattern) (ha : d4602 p = 1) (hb : d73191 p = 1) : d73312 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4597 q = 1) (hb : d73191 q = 1) : d73307 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d4597, d73307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4597, d73307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7324 q ha hb
  have h2 (q : Pattern) (ha : d4598 q = 1) (hb : d73191 q = 1) : d73308 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d4598, d73308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4598, d73308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4599 q = 1) (hb : d73191 q = 1) : d73309 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d4599, d73309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4599, d73309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4600 q = 1) (hb : d73191 q = 1) : d73310 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d4600, d73310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4600, d73310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4601 q = 1) (hb : d73191 q = 1) : d73311 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d4601, d73311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4601, d73311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4602 q = 1) (hb : d73191 q = 1) : d73312 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d4602, d73312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4602, d73312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7326 (p : Pattern) (ha : d4608 p = 1) (hb : d73191 p = 1) : d73318 p = 1 := by
  have h0 (q : Pattern) (ha : d4445 q = 1) (hb : d73191 q = 1) : d73239 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d4445, d73239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7315 q ha hb
    | true =>
      simp only [d4445, d73239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7317 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4483 q = 1) (hb : d73191 q = 1) : d73256 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d4483, d73256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4483, d73256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7319 q ha hb
  have h3 (q : Pattern) (ha : d4484 q = 1) (hb : d73191 q = 1) : d73257 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d4484, d73257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4484, d73257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4522 q = 1) (hb : d73191 q = 1) : d73274 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d4522, d73274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4522, d73274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7321 q ha hb
  have h5 (q : Pattern) (ha : d4523 q = 1) (hb : d73191 q = 1) : d73275 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d4523, d73275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4523, d73275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4524 q = 1) (hb : d73191 q = 1) : d73276 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d4524, d73276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4524, d73276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4562 q = 1) (hb : d73191 q = 1) : d73293 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d4562, d73293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4562, d73293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7323 q ha hb
  have h8 (q : Pattern) (ha : d4563 q = 1) (hb : d73191 q = 1) : d73294 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d4563, d73294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4563, d73294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4564 q = 1) (hb : d73191 q = 1) : d73295 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d4564, d73295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4564, d73295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4565 q = 1) (hb : d73191 q = 1) : d73296 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d4565, d73296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4565, d73296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4603 q = 1) (hb : d73191 q = 1) : d73313 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d4603, d73313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4603, d73313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7325 q ha hb
  have h12 (q : Pattern) (ha : d4604 q = 1) (hb : d73191 q = 1) : d73314 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d4604, d73314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4604, d73314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d4605 q = 1) (hb : d73191 q = 1) : d73315 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d4605, d73315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4605, d73315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d4606 q = 1) (hb : d73191 q = 1) : d73316 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d4606, d73316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4606, d73316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d4607 q = 1) (hb : d73191 q = 1) : d73317 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d4607, d73317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4607, d73317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d4608 q = 1) (hb : d73191 q = 1) : d73318 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d4608, d73318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d4608, d73318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro7327 (p : Pattern) (ha : d4614 p = 1) (hb : d73191 p = 1) : d73324 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4609 q = 1) (hb : d73191 q = 1) : d73319 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d4609, d73319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7326 q ha hb
    | true =>
      simp only [d4609, d73319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4610 q = 1) (hb : d73191 q = 1) : d73320 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d4610, d73320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4610, d73320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4611 q = 1) (hb : d73191 q = 1) : d73321 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d4611, d73321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4611, d73321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4612 q = 1) (hb : d73191 q = 1) : d73322 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d4612, d73322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4612, d73322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4613 q = 1) (hb : d73191 q = 1) : d73323 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d4613, d73323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4613, d73323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4614 q = 1) (hb : d73191 q = 1) : d73324 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d4614, d73324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4614, d73324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7328 (p : Pattern) (ha : d4620 p = 1) (hb : d73191 p = 1) : d73330 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4615 q = 1) (hb : d73191 q = 1) : d73325 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d4615, d73325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7327 q ha hb
    | true =>
      simp only [d4615, d73325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4616 q = 1) (hb : d73191 q = 1) : d73326 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d4616, d73326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4616, d73326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4617 q = 1) (hb : d73191 q = 1) : d73327 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d4617, d73327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4617, d73327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4618 q = 1) (hb : d73191 q = 1) : d73328 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d4618, d73328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4618, d73328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4619 q = 1) (hb : d73191 q = 1) : d73329 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d4619, d73329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4619, d73329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4620 q = 1) (hb : d73191 q = 1) : d73330 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d4620, d73330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4620, d73330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7329 (p : Pattern) (ha : d4626 p = 1) (hb : d73191 p = 1) : d73336 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4621 q = 1) (hb : d73191 q = 1) : d73331 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d4621, d73331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7328 q ha hb
    | true =>
      simp only [d4621, d73331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4622 q = 1) (hb : d73191 q = 1) : d73332 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d4622, d73332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4622, d73332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4623 q = 1) (hb : d73191 q = 1) : d73333 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d4623, d73333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4623, d73333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4624 q = 1) (hb : d73191 q = 1) : d73334 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d4624, d73334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4624, d73334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4625 q = 1) (hb : d73191 q = 1) : d73335 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d4625, d73335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4625, d73335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4626 q = 1) (hb : d73191 q = 1) : d73336 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d4626, d73336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4626, d73336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7330 (p : Pattern) (ha : d4632 p = 1) (hb : d73191 p = 1) : d73342 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4627 q = 1) (hb : d73191 q = 1) : d73337 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d4627, d73337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7329 q ha hb
    | true =>
      simp only [d4627, d73337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4628 q = 1) (hb : d73191 q = 1) : d73338 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d4628, d73338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4628, d73338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4629 q = 1) (hb : d73191 q = 1) : d73339 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d4629, d73339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4629, d73339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4630 q = 1) (hb : d73191 q = 1) : d73340 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d4630, d73340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4630, d73340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4631 q = 1) (hb : d73191 q = 1) : d73341 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d4631, d73341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4631, d73341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4632 q = 1) (hb : d73191 q = 1) : d73342 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d4632, d73342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4632, d73342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7331 (p : Pattern) (ha : d4638 p = 1) (hb : d73191 p = 1) : d73348 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4633 q = 1) (hb : d73191 q = 1) : d73343 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d4633, d73343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7330 q ha hb
    | true =>
      simp only [d4633, d73343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4634 q = 1) (hb : d73191 q = 1) : d73344 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d4634, d73344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4634, d73344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4635 q = 1) (hb : d73191 q = 1) : d73345 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d4635, d73345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4635, d73345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4636 q = 1) (hb : d73191 q = 1) : d73346 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d4636, d73346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4636, d73346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4637 q = 1) (hb : d73191 q = 1) : d73347 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d4637, d73347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4637, d73347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4638 q = 1) (hb : d73191 q = 1) : d73348 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d4638, d73348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4638, d73348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7332 (p : Pattern) (ha : d4644 p = 1) (hb : d73191 p = 1) : d73354 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4639 q = 1) (hb : d73191 q = 1) : d73349 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d4639, d73349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7331 q ha hb
    | true =>
      simp only [d4639, d73349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4640 q = 1) (hb : d73191 q = 1) : d73350 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d4640, d73350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4640, d73350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4641 q = 1) (hb : d73191 q = 1) : d73351 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d4641, d73351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4641, d73351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4642 q = 1) (hb : d73191 q = 1) : d73352 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d4642, d73352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4642, d73352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4643 q = 1) (hb : d73191 q = 1) : d73353 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d4643, d73353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4643, d73353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4644 q = 1) (hb : d73191 q = 1) : d73354 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d4644, d73354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4644, d73354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7333 (p : Pattern) (ha : d4650 p = 1) (hb : d73191 p = 1) : d73360 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4645 q = 1) (hb : d73191 q = 1) : d73355 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d4645, d73355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7332 q ha hb
    | true =>
      simp only [d4645, d73355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4646 q = 1) (hb : d73191 q = 1) : d73356 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d4646, d73356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4646, d73356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4647 q = 1) (hb : d73191 q = 1) : d73357 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d4647, d73357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4647, d73357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4648 q = 1) (hb : d73191 q = 1) : d73358 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d4648, d73358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4648, d73358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4649 q = 1) (hb : d73191 q = 1) : d73359 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d4649, d73359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4649, d73359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4650 q = 1) (hb : d73191 q = 1) : d73360 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d4650, d73360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4650, d73360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7334 (p : Pattern) (ha : d52013 p = 1) (hb : d73194 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d51894 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d370 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d370, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30 q ha hb
    | true =>
      simp only [d370, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d371 q = 1) (hb : d52009 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371, d52009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d371, d52009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d52010 q = 1) (hb : d69433 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52010, d69433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d52010, d69433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d52011 q = 1) (hb : d73192 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52011, d73192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d52011, d73192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d52012 q = 1) (hb : d73193 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52012, d73193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52012, d73193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d52013 q = 1) (hb : d73194 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52013, d73194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52013, d73194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro7335 (p : Pattern) (ha : d52029 p = 1) (hb : d73195 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51894 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d370 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d370, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30 q ha hb
    | true =>
      simp only [d370, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d371 q = 1) (hb : d52009 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371, d52009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d371, d52009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d52010 q = 1) (hb : d69433 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52010, d69433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d52010, d69433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d52011 q = 1) (hb : d73192 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52011, d73192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52011, d73192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d52012 q = 1) (hb : d73193 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52012, d73193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52012, d73193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d52018 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d52022 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d51901 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d390 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d390, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22 q ha hb
    | true =>
      simp only [d390, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d391 q = 1) (hb : d52025 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d391, d52025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d391, d52025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d50 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h19 (q : Pattern) (ha : d51 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h20 (q : Pattern) (ha : d52026 q = 1) (hb : d69437 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52026, d69437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
    | true =>
      simp only [d52026, d69437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d52027 q = 1) (hb : d69445 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52027, d69445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d52027, d69445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d52028 q = 1) (hb : d69446 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52028, d69446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d52028, d69446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d52029 q = 1) (hb : d73195 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52029, d73195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d52029, d73195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro7336 (p : Pattern) (ha : d52038 p = 1) (hb : d69447 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51901 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d390 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d390, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22 q ha hb
    | true =>
      simp only [d390, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d391 q = 1) (hb : d52025 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d391, d52025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d391, d52025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d50 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d51 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d52026 q = 1) (hb : d69437 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52026, d69437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52026, d69437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d52036 q = 1) (hb : d69445 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52036, d69445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52036, d69445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d52037 q = 1) (hb : d69446 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52037, d69446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52037, d69446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52038 q = 1) (hb : d69447 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52038, d69447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52038, d69447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7337 (p : Pattern) (ha : d52067 p = 1) (hb : d69456 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51935 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d451 q = 1) (hb : d52062 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d451, d52062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26 q ha hb
    | true =>
      simp only [d451, d52062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d452 q = 1) (hb : d52063 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d452, d52063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d452, d52063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
    | true =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85 q = 1) (hb : d51937 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, d51937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85, d51937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d52064 q = 1) (hb : d69453 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52064, d69453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52064, d69453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d52065 q = 1) (hb : d69454 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52065, d69454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52065, d69454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d52066 q = 1) (hb : d69455 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52066, d69455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52066, d69455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52067 q = 1) (hb : d69456 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52067, d69456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52067, d69456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7338 (p : Pattern) (ha : d58438 p = 1) (hb : d73201 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51966 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52030 q = 1) (hb : d73196 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52030, d73196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7334 q ha hb
    | true =>
      simp only [d52030, d73196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7335 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d58434 q = 1) (hb : d73197 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58434, d73197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58434, d73197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d58435 q = 1) (hb : d73198 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58435, d73198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58435, d73198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h5 (q : Pattern) (ha : d58436 q = 1) (hb : d73199 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58436, d73199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58436, d73199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52039 q = 1) (hb : d69448 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52039, d69448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d52039, d69448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7336 q ha hb
  have h7 (q : Pattern) (ha : d52040 q = 1) (hb : d69449 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52040, d69449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52040, d69449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h8 (q : Pattern) (ha : d52041 q = 1) (hb : d69450 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52041, d69450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52041, d69450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h9 (q : Pattern) (ha : d52042 q = 1) (hb : d69451 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52042, d69451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d52042, d69451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h10 (q : Pattern) (ha : d58437 q = 1) (hb : d73200 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58437, d73200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58437, d73200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d52068 q = 1) (hb : d69457 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52068, d69457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d52068, d69457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7337 q ha hb
  have h12 (q : Pattern) (ha : d52069 q = 1) (hb : d69458 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52069, d69458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d52069, d69458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h13 (q : Pattern) (ha : d52070 q = 1) (hb : d69459 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52070, d69459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d52070, d69459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h14 (q : Pattern) (ha : d52071 q = 1) (hb : d69460 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52071, d69460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d52071, d69460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h15 (q : Pattern) (ha : d52072 q = 1) (hb : d69461 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52072, d69461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d52072, d69461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h16 (q : Pattern) (ha : d58438 q = 1) (hb : d73201 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58438, d73201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d58438, d73201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro7339 (p : Pattern) (ha : d52143 p = 1) (hb : d73209 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52099 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52105 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52007 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4711 q = 1) (hb : d52136 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4711, d52136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53 q ha hb
    | true =>
      simp only [d4711, d52136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d52137 q = 1) (hb : d69468 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52137, d69468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52137, d69468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d370 q = 1) (hb : d52138 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d370, d52138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30 q ha hb
    | true =>
      simp only [d370, d52138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d371 q = 1) (hb : d52139 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371, d52139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d371, d52139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d52140 q = 1) (hb : d69469 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52140, d69469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52140, d69469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d52141 q = 1) (hb : d73207 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52141, d73207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d52141, d73207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d52142 q = 1) (hb : d73208 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52142, d73208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52142, d73208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d52143 q = 1) (hb : d73209 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52143, d73209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52143, d73209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro7340 (p : Pattern) (ha : d52161 p = 1) (hb : d73210 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52105 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52007 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4711 q = 1) (hb : d52136 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4711, d52136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53 q ha hb
    | true =>
      simp only [d4711, d52136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d52137 q = 1) (hb : d69468 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52137, d69468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d52137, d69468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d370 q = 1) (hb : d52138 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d370, d52138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30 q ha hb
    | true =>
      simp only [d370, d52138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d371 q = 1) (hb : d52139 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371, d52139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d371, d52139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d52140 q = 1) (hb : d69469 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52140, d69469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52140, d69469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d52141 q = 1) (hb : d73207 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52141, d73207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52141, d73207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d52142 q = 1) (hb : d73208 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52142, d73208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52142, d73208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d52148 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d52152 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52023 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d4725 q = 1) (hb : d52154 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4725, d52154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45 q ha hb
    | true =>
      simp only [d4725, d52154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d52155 q = 1) (hb : d69473 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52155, d69473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d52155, d69473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d390 q = 1) (hb : d52156 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d390, d52156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22 q ha hb
    | true =>
      simp only [d390, d52156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h19 (q : Pattern) (ha : d391 q = 1) (hb : d52157 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d391, d52157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d391, d52157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h20 (q : Pattern) (ha : d52158 q = 1) (hb : d69474 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52158, d69474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d52158, d69474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d52159 q = 1) (hb : d69482 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52159, d69482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d52159, d69482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d52160 q = 1) (hb : d69483 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52160, d69483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d52160, d69483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d52161 q = 1) (hb : d73210 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52161, d73210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d52161, d73210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro7341 (p : Pattern) (ha : d52170 p = 1) (hb : d69484 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52023 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4725 q = 1) (hb : d52154 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4725, d52154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45 q ha hb
    | true =>
      simp only [d4725, d52154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d52155 q = 1) (hb : d69473 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52155, d69473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d52155, d69473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d390 q = 1) (hb : d52156 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d390, d52156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22 q ha hb
    | true =>
      simp only [d390, d52156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d391 q = 1) (hb : d52157 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d391, d52157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d391, d52157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d52158 q = 1) (hb : d69474 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52158, d69474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d52158, d69474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d52168 q = 1) (hb : d69482 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52168, d69482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52168, d69482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d52169 q = 1) (hb : d69483 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52169, d69483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52169, d69483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52170 q = 1) (hb : d69484 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52170, d69484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52170, d69484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7342 (p : Pattern) (ha : d52203 p = 1) (hb : d69494 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52061 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4755 q = 1) (hb : d52196 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4755, d52196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49 q ha hb
    | true =>
      simp only [d4755, d52196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52062 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d52197 q = 1) (hb : d69490 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52197, d69490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d52197, d69490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d451 q = 1) (hb : d52198 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d451, d52198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26 q ha hb
    | true =>
      simp only [d451, d52198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d452 q = 1) (hb : d52199 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d452, d52199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d452, d52199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d52200 q = 1) (hb : d69491 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52200, d69491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d52200, d69491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d52201 q = 1) (hb : d69492 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52201, d69492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52201, d69492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d52202 q = 1) (hb : d69493 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52202, d69493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52202, d69493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52203 q = 1) (hb : d69494 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52203, d69494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52203, d69494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7343 (p : Pattern) (ha : d58455 p = 1) (hb : d73216 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52093 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52162 q = 1) (hb : d73211 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52162, d73211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7339 q ha hb
    | true =>
      simp only [d52162, d73211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7340 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d58444 q = 1) (hb : d73212 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58444, d73212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58444, d73212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d58445 q = 1) (hb : d73213 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58445, d73213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58445, d73213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h5 (q : Pattern) (ha : d58446 q = 1) (hb : d73214 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58446, d73214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58446, d73214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52171 q = 1) (hb : d69485 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52171, d69485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d52171, d69485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7341 q ha hb
  have h7 (q : Pattern) (ha : d58447 q = 1) (hb : d69486 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58447, d69486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58447, d69486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h8 (q : Pattern) (ha : d58448 q = 1) (hb : d69487 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58448, d69487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d58448, d69487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h9 (q : Pattern) (ha : d58449 q = 1) (hb : d69488 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58449, d69488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d58449, d69488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h10 (q : Pattern) (ha : d58450 q = 1) (hb : d73215 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58450, d73215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58450, d73215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d52204 q = 1) (hb : d69495 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52204, d69495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d52204, d69495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7342 q ha hb
  have h12 (q : Pattern) (ha : d58451 q = 1) (hb : d69496 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58451, d69496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d58451, d69496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h13 (q : Pattern) (ha : d58452 q = 1) (hb : d69497 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58452, d69497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d58452, d69497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h14 (q : Pattern) (ha : d58453 q = 1) (hb : d69498 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58453, d69498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d58453, d69498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h15 (q : Pattern) (ha : d58454 q = 1) (hb : d69499 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58454, d69499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d58454, d69499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h16 (q : Pattern) (ha : d58455 q = 1) (hb : d73216 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58455, d73216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d58455, d73216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro7344 (p : Pattern) (ha : d58461 p = 1) (hb : d73222 p = 1) : d0 p = 1 := by
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
  have h5 (q : Pattern) (ha : d58439 q = 1) (hb : d73202 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58439, d73202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58439, d73202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7338 q ha hb
  have h6 (q : Pattern) (ha : d58440 q = 1) (hb : d73203 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58440, d73203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58440, d73203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d58441 q = 1) (hb : d73204 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58441, d73204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58441, d73204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d58442 q = 1) (hb : d73205 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58442, d73205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58442, d73205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d58443 q = 1) (hb : d73206 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58443, d73206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d58443, d73206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d58456 q = 1) (hb : d73217 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58456, d73217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58456, d73217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7343 q ha hb
  have h11 (q : Pattern) (ha : d58457 q = 1) (hb : d73218 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58457, d73218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58457, d73218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d58458 q = 1) (hb : d73219 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58458, d73219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58458, d73219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d58459 q = 1) (hb : d73220 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58459, d73220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58459, d73220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d58460 q = 1) (hb : d73221 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58460, d73221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58460, d73221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d58461 q = 1) (hb : d73222 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58461, d73222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d58461, d73222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro7345 (p : Pattern) (ha : d52315 p = 1) (hb : d73225 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52265 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52274 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52234 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4796 q = 1) (hb : d52308 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4796, d52308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91 q ha hb
    | true =>
      simp only [d4796, d52308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52239 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d52309 q = 1) (hb : d69507 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52309, d69507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52309, d69507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d603 q = 1) (hb : d52310 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d603, d52310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62 q ha hb
    | true =>
      simp only [d603, d52310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d604 q = 1) (hb : d52311 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d604, d52311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d604, d52311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d52312 q = 1) (hb : d69508 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52312, d69508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52312, d69508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d52313 q = 1) (hb : d73223 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52313, d73223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d52313, d73223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d52314 q = 1) (hb : d73224 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52314, d73224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52314, d73224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d52315 q = 1) (hb : d73225 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52315, d73225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52315, d73225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro7346 (p : Pattern) (ha : d52335 p = 1) (hb : d73226 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52265 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52274 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52234 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4796 q = 1) (hb : d52308 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4796, d52308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91 q ha hb
    | true =>
      simp only [d4796, d52308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52239 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d52309 q = 1) (hb : d69507 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52309, d69507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d52309, d69507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d603 q = 1) (hb : d52310 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d603, d52310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62 q ha hb
    | true =>
      simp only [d603, d52310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d604 q = 1) (hb : d52311 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d604, d52311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d604, d52311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d52312 q = 1) (hb : d69508 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52312, d69508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52312, d69508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d52313 q = 1) (hb : d73223 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52313, d73223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52313, d73223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d52314 q = 1) (hb : d73224 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52314, d73224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52314, d73224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d52321 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d52326 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52247 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d4810 q = 1) (hb : d52328 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4810, d52328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79 q ha hb
    | true =>
      simp only [d4810, d52328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d52249 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d52329 q = 1) (hb : d69512 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52329, d69512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d52329, d69512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d626 q = 1) (hb : d52330 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d626, d52330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65 q ha hb
    | true =>
      simp only [d626, d52330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h19 (q : Pattern) (ha : d627 q = 1) (hb : d52331 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d627, d52331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d627, d52331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h20 (q : Pattern) (ha : d52332 q = 1) (hb : d69513 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52332, d69513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d52332, d69513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d52333 q = 1) (hb : d69521 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52333, d69521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d52333, d69521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d52334 q = 1) (hb : d69522 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52334, d69522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d52334, d69522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d52335 q = 1) (hb : d73226 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52335, d73226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d52335, d73226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro7347 (p : Pattern) (ha : d52355 p = 1) (hb : d69523 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52247 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4810 q = 1) (hb : d52328 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4810, d52328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79 q ha hb
    | true =>
      simp only [d4810, d52328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52249 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d52329 q = 1) (hb : d69512 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52329, d69512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d52329, d69512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d626 q = 1) (hb : d52330 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d626, d52330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65 q ha hb
    | true =>
      simp only [d626, d52330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d627 q = 1) (hb : d52331 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d627, d52331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d627, d52331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d52332 q = 1) (hb : d69513 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52332, d69513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d52332, d69513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d52353 q = 1) (hb : d69521 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52353, d69521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52353, d69521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d52354 q = 1) (hb : d69522 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52354, d69522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52354, d69522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52355 q = 1) (hb : d69523 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52355, d69523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52355, d69523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7348 (p : Pattern) (ha : d52406 p = 1) (hb : d69533 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52393 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4849 q = 1) (hb : d52394 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4849, d52394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro84 q ha hb
    | true =>
      simp only [d4849, d52394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52399 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d52400 q = 1) (hb : d69529 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52400, d69529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d52400, d69529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d720 q = 1) (hb : d52401 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d720, d52401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85 q ha hb
    | true =>
      simp only [d720, d52401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d721 q = 1) (hb : d52402 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d721, d52402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d721, d52402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d52403 q = 1) (hb : d69530 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52403, d69530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d52403, d69530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d52404 q = 1) (hb : d69531 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52404, d69531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52404, d69531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d52405 q = 1) (hb : d69532 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52405, d69532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52405, d69532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52406 q = 1) (hb : d69533 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52406, d69533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52406, d69533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7349 (p : Pattern) (ha : d58473 p = 1) (hb : d73232 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52257 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52336 q = 1) (hb : d73227 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52336, d73227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7345 q ha hb
    | true =>
      simp only [d52336, d73227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7346 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d58462 q = 1) (hb : d73228 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58462, d73228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58462, d73228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d58463 q = 1) (hb : d73229 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58463, d73229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58463, d73229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h5 (q : Pattern) (ha : d58464 q = 1) (hb : d73230 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58464, d73230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58464, d73230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52356 q = 1) (hb : d69524 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52356, d69524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d52356, d69524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7347 q ha hb
  have h7 (q : Pattern) (ha : d58465 q = 1) (hb : d69525 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58465, d69525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58465, d69525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h8 (q : Pattern) (ha : d58466 q = 1) (hb : d69526 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58466, d69526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d58466, d69526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h9 (q : Pattern) (ha : d58467 q = 1) (hb : d69527 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58467, d69527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d58467, d69527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h10 (q : Pattern) (ha : d58468 q = 1) (hb : d73231 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58468, d73231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58468, d73231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d52407 q = 1) (hb : d69534 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52407, d69534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d52407, d69534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7348 q ha hb
  have h12 (q : Pattern) (ha : d58469 q = 1) (hb : d69535 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58469, d69535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d58469, d69535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h13 (q : Pattern) (ha : d58470 q = 1) (hb : d69536 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58470, d69536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d58470, d69536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h14 (q : Pattern) (ha : d58471 q = 1) (hb : d69537 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58471, d69537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d58471, d69537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h15 (q : Pattern) (ha : d58472 q = 1) (hb : d69538 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58472, d69538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d58472, d69538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h16 (q : Pattern) (ha : d58473 q = 1) (hb : d73232 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58473, d73232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d58473, d73232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro7350 (p : Pattern) (ha : d58479 p = 1) (hb : d73238 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58474 q = 1) (hb : d73233 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58474, d73233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58474, d73233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7349 q ha hb
  have h2 (q : Pattern) (ha : d58475 q = 1) (hb : d73234 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58475, d73234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58475, d73234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d58476 q = 1) (hb : d73235 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58476, d73235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58476, d73235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58477 q = 1) (hb : d73236 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58477, d73236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58477, d73236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58478 q = 1) (hb : d73237 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58478, d73237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58478, d73237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58479 q = 1) (hb : d73238 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58479, d73238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58479, d73238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7351 (p : Pattern) (ha : d52536 p = 1) (hb : d73242 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52487 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52496 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52456 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4891 q = 1) (hb : d52529 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4891, d52529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro138 q ha hb
    | true =>
      simp only [d4891, d52529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52461 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d52530 q = 1) (hb : d69547 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52530, d69547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52530, d69547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d909 q = 1) (hb : d52531 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d909, d52531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106 q ha hb
    | true =>
      simp only [d909, d52531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d910 q = 1) (hb : d52532 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d910, d52532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d910, d52532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d52533 q = 1) (hb : d69548 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52533, d69548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52533, d69548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d52534 q = 1) (hb : d73240 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52534, d73240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d52534, d73240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d52535 q = 1) (hb : d73241 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52535, d73241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52535, d73241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d52536 q = 1) (hb : d73242 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52536, d73242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52536, d73242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro7352 (p : Pattern) (ha : d52556 p = 1) (hb : d73243 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52496 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52456 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4891 q = 1) (hb : d52529 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4891, d52529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro138 q ha hb
    | true =>
      simp only [d4891, d52529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52461 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d52530 q = 1) (hb : d69547 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52530, d69547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d52530, d69547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d909 q = 1) (hb : d52531 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d909, d52531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106 q ha hb
    | true =>
      simp only [d909, d52531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d910 q = 1) (hb : d52532 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d910, d52532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d910, d52532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d52533 q = 1) (hb : d69548 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52533, d69548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52533, d69548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d52534 q = 1) (hb : d73240 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52534, d73240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52534, d73240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d52535 q = 1) (hb : d73241 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52535, d73241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52535, d73241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d52542 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d52547 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52469 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d4905 q = 1) (hb : d52549 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4905, d52549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro125 q ha hb
    | true =>
      simp only [d4905, d52549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d52471 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d52550 q = 1) (hb : d69552 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52550, d69552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d52550, d69552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d932 q = 1) (hb : d52551 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d932, d52551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro109 q ha hb
    | true =>
      simp only [d932, d52551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h19 (q : Pattern) (ha : d933 q = 1) (hb : d52552 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d933, d52552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d933, d52552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h20 (q : Pattern) (ha : d52553 q = 1) (hb : d69553 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52553, d69553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d52553, d69553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d52554 q = 1) (hb : d69561 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52554, d69561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d52554, d69561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d52555 q = 1) (hb : d69562 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52555, d69562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d52555, d69562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d52556 q = 1) (hb : d73243 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52556, d73243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d52556, d73243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro7353 (p : Pattern) (ha : d52576 p = 1) (hb : d69563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52469 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4905 q = 1) (hb : d52549 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4905, d52549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro125 q ha hb
    | true =>
      simp only [d4905, d52549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52471 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d52550 q = 1) (hb : d69552 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52550, d69552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d52550, d69552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d932 q = 1) (hb : d52551 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d932, d52551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro109 q ha hb
    | true =>
      simp only [d932, d52551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d933 q = 1) (hb : d52552 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d933, d52552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d933, d52552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d52553 q = 1) (hb : d69553 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52553, d69553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d52553, d69553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d52574 q = 1) (hb : d69561 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52574, d69561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52574, d69561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d52575 q = 1) (hb : d69562 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52575, d69562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52575, d69562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52576 q = 1) (hb : d69563 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52576, d69563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52576, d69563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7354 (p : Pattern) (ha : d52643 p = 1) (hb : d69573 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52630 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4944 q = 1) (hb : d52631 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4944, d52631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro131 q ha hb
    | true =>
      simp only [d4944, d52631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52636 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d52637 q = 1) (hb : d69569 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52637, d69569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d52637, d69569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1053 q = 1) (hb : d52638 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1053, d52638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro132 q ha hb
    | true =>
      simp only [d1053, d52638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1054 q = 1) (hb : d52639 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1054, d52639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1054, d52639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d52640 q = 1) (hb : d69570 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52640, d69570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d52640, d69570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d52641 q = 1) (hb : d69571 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52641, d69571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52641, d69571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d52642 q = 1) (hb : d69572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52642, d69572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52642, d69572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52643 q = 1) (hb : d69573 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52643, d69573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52643, d69573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7355 (p : Pattern) (ha : d58492 p = 1) (hb : d73249 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52479 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52557 q = 1) (hb : d73244 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52557, d73244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7351 q ha hb
    | true =>
      simp only [d52557, d73244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7352 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d58481 q = 1) (hb : d73245 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58481, d73245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58481, d73245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d58482 q = 1) (hb : d73246 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58482, d73246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58482, d73246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h5 (q : Pattern) (ha : d58483 q = 1) (hb : d73247 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58483, d73247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58483, d73247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52577 q = 1) (hb : d69564 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52577, d69564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d52577, d69564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7353 q ha hb
  have h7 (q : Pattern) (ha : d58484 q = 1) (hb : d69565 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58484, d69565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58484, d69565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h8 (q : Pattern) (ha : d58485 q = 1) (hb : d69566 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58485, d69566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d58485, d69566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h9 (q : Pattern) (ha : d58486 q = 1) (hb : d69567 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58486, d69567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d58486, d69567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h10 (q : Pattern) (ha : d58487 q = 1) (hb : d73248 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58487, d73248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58487, d73248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d52644 q = 1) (hb : d69574 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52644, d69574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d52644, d69574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7354 q ha hb
  have h12 (q : Pattern) (ha : d58488 q = 1) (hb : d69575 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58488, d69575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d58488, d69575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h13 (q : Pattern) (ha : d58489 q = 1) (hb : d69576 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58489, d69576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d58489, d69576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h14 (q : Pattern) (ha : d58490 q = 1) (hb : d69577 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58490, d69577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d58490, d69577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h15 (q : Pattern) (ha : d58491 q = 1) (hb : d69578 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58491, d69578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d58491, d69578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h16 (q : Pattern) (ha : d58492 q = 1) (hb : d73249 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58492, d73249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d58492, d73249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro7356 (p : Pattern) (ha : d58498 p = 1) (hb : d73255 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58493 q = 1) (hb : d73250 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58493, d73250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58493, d73250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7355 q ha hb
  have h2 (q : Pattern) (ha : d58494 q = 1) (hb : d73251 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58494, d73251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58494, d73251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d58495 q = 1) (hb : d73252 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58495, d73252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58495, d73252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58496 q = 1) (hb : d73253 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58496, d73253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58496, d73253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58497 q = 1) (hb : d73254 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58497, d73254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58497, d73254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58498 q = 1) (hb : d73255 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58498, d73255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58498, d73255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7357 (p : Pattern) (ha : d52816 p = 1) (hb : d73260 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52770 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52779 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52739 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4987 q = 1) (hb : d52809 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4987, d52809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro190 q ha hb
    | true =>
      simp only [d4987, d52809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52744 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d52810 q = 1) (hb : d69588 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52810, d69588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52810, d69588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d1320 q = 1) (hb : d52811 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1320, d52811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro158 q ha hb
    | true =>
      simp only [d1320, d52811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1321 q = 1) (hb : d52812 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1321, d52812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1321, d52812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d52813 q = 1) (hb : d69589 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52813, d69589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52813, d69589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d52814 q = 1) (hb : d73258 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52814, d73258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d52814, d73258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d52815 q = 1) (hb : d73259 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52815, d73259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52815, d73259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d52816 q = 1) (hb : d73260 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52816, d73260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52816, d73260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro7358 (p : Pattern) (ha : d52836 p = 1) (hb : d73261 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52770 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52779 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52739 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4987 q = 1) (hb : d52809 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4987, d52809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro190 q ha hb
    | true =>
      simp only [d4987, d52809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52744 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d52810 q = 1) (hb : d69588 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52810, d69588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d52810, d69588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1320 q = 1) (hb : d52811 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1320, d52811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro158 q ha hb
    | true =>
      simp only [d1320, d52811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1321 q = 1) (hb : d52812 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1321, d52812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1321, d52812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d52813 q = 1) (hb : d69589 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52813, d69589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52813, d69589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d52814 q = 1) (hb : d73258 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52814, d73258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52814, d73258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d52815 q = 1) (hb : d73259 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52815, d73259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52815, d73259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d52822 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d52827 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52752 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d5001 q = 1) (hb : d52829 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5001, d52829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro177 q ha hb
    | true =>
      simp only [d5001, d52829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d52754 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d52830 q = 1) (hb : d69593 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52830, d69593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d52830, d69593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d1343 q = 1) (hb : d52831 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1343, d52831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro161 q ha hb
    | true =>
      simp only [d1343, d52831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h19 (q : Pattern) (ha : d1344 q = 1) (hb : d52832 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1344, d52832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d1344, d52832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h20 (q : Pattern) (ha : d52833 q = 1) (hb : d69594 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52833, d69594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d52833, d69594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d52834 q = 1) (hb : d69602 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52834, d69602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d52834, d69602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d52835 q = 1) (hb : d69603 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52835, d69603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d52835, d69603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d52836 q = 1) (hb : d73261 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52836, d73261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d52836, d73261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro7359 (p : Pattern) (ha : d52856 p = 1) (hb : d69604 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52752 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5001 q = 1) (hb : d52829 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5001, d52829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro177 q ha hb
    | true =>
      simp only [d5001, d52829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52754 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d52830 q = 1) (hb : d69593 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52830, d69593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d52830, d69593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1343 q = 1) (hb : d52831 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1343, d52831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro161 q ha hb
    | true =>
      simp only [d1343, d52831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1344 q = 1) (hb : d52832 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1344, d52832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1344, d52832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d52833 q = 1) (hb : d69594 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52833, d69594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d52833, d69594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d52854 q = 1) (hb : d69602 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52854, d69602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52854, d69602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d52855 q = 1) (hb : d69603 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52855, d69603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52855, d69603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52856 q = 1) (hb : d69604 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52856, d69604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52856, d69604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7360 (p : Pattern) (ha : d52937 p = 1) (hb : d69614 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52924 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5054 q = 1) (hb : d52925 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5054, d52925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro183 q ha hb
    | true =>
      simp only [d5054, d52925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52930 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d52931 q = 1) (hb : d69610 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52931, d69610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d52931, d69610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1487 q = 1) (hb : d52932 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1487, d52932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro184 q ha hb
    | true =>
      simp only [d1487, d52932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1488 q = 1) (hb : d52933 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1488, d52933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1488, d52933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d52934 q = 1) (hb : d69611 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52934, d69611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d52934, d69611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d52935 q = 1) (hb : d69612 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52935, d69612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52935, d69612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d52936 q = 1) (hb : d69613 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52936, d69613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52936, d69613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52937 q = 1) (hb : d69614 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52937, d69614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52937, d69614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7361 (p : Pattern) (ha : d58512 p = 1) (hb : d73267 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52837 q = 1) (hb : d73262 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52837, d73262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7357 q ha hb
    | true =>
      simp only [d52837, d73262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7358 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d58501 q = 1) (hb : d73263 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58501, d73263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58501, d73263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d58502 q = 1) (hb : d73264 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58502, d73264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58502, d73264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h5 (q : Pattern) (ha : d58503 q = 1) (hb : d73265 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58503, d73265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58503, d73265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52857 q = 1) (hb : d69605 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52857, d69605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d52857, d69605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7359 q ha hb
  have h7 (q : Pattern) (ha : d58504 q = 1) (hb : d69606 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58504, d69606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58504, d69606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h8 (q : Pattern) (ha : d58505 q = 1) (hb : d69607 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58505, d69607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d58505, d69607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h9 (q : Pattern) (ha : d58506 q = 1) (hb : d69608 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58506, d69608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d58506, d69608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h10 (q : Pattern) (ha : d58507 q = 1) (hb : d73266 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58507, d73266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58507, d73266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d52938 q = 1) (hb : d69615 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52938, d69615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d52938, d69615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7360 q ha hb
  have h12 (q : Pattern) (ha : d58508 q = 1) (hb : d69616 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58508, d69616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d58508, d69616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h13 (q : Pattern) (ha : d58509 q = 1) (hb : d69617 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58509, d69617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d58509, d69617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h14 (q : Pattern) (ha : d58510 q = 1) (hb : d69618 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58510, d69618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d58510, d69618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h15 (q : Pattern) (ha : d58511 q = 1) (hb : d69619 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58511, d69619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d58511, d69619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h16 (q : Pattern) (ha : d58512 q = 1) (hb : d73267 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58512, d73267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d58512, d73267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro7362 (p : Pattern) (ha : d58518 p = 1) (hb : d73273 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58513 q = 1) (hb : d73268 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58513, d73268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58513, d73268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7361 q ha hb
  have h2 (q : Pattern) (ha : d58514 q = 1) (hb : d73269 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58514, d73269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58514, d73269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d58515 q = 1) (hb : d73270 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58515, d73270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58515, d73270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58516 q = 1) (hb : d73271 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58516, d73271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58516, d73271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58517 q = 1) (hb : d73272 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58517, d73272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58517, d73272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58518 q = 1) (hb : d73273 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58518, d73273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58518, d73273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7363 (p : Pattern) (ha : d53131 p = 1) (hb : d73279 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53091 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53100 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53060 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5098 q = 1) (hb : d53124 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5098, d53124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro246 q ha hb
    | true =>
      simp only [d5098, d53124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53065 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d53125 q = 1) (hb : d69630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53125, d69630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d53125, d69630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d1797 q = 1) (hb : d53126 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1797, d53126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro216 q ha hb
    | true =>
      simp only [d1797, d53126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1798 q = 1) (hb : d53127 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1798, d53127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1798, d53127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53128 q = 1) (hb : d69631 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53128, d69631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53128, d69631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d53129 q = 1) (hb : d73277 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53129, d73277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d53129, d73277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53130 q = 1) (hb : d73278 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53130, d73278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53130, d73278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d53131 q = 1) (hb : d73279 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53131, d73279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53131, d73279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro7364 (p : Pattern) (ha : d53151 p = 1) (hb : d73280 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53091 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53100 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53060 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5098 q = 1) (hb : d53124 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5098, d53124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro246 q ha hb
    | true =>
      simp only [d5098, d53124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53065 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53125 q = 1) (hb : d69630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53125, d69630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d53125, d69630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1797 q = 1) (hb : d53126 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1797, d53126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro216 q ha hb
    | true =>
      simp only [d1797, d53126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1798 q = 1) (hb : d53127 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1798, d53127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1798, d53127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d53128 q = 1) (hb : d69631 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53128, d69631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53128, d69631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d53129 q = 1) (hb : d73277 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53129, d73277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53129, d73277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53130 q = 1) (hb : d73278 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53130, d73278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53130, d73278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d53137 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d53142 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53073 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d5112 q = 1) (hb : d53144 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5112, d53144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro233 q ha hb
    | true =>
      simp only [d5112, d53144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d53075 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d53145 q = 1) (hb : d69635 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53145, d69635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d53145, d69635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d1820 q = 1) (hb : d53146 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1820, d53146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro219 q ha hb
    | true =>
      simp only [d1820, d53146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h19 (q : Pattern) (ha : d1821 q = 1) (hb : d53147 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1821, d53147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d1821, d53147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h20 (q : Pattern) (ha : d53148 q = 1) (hb : d69636 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53148, d69636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d53148, d69636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d53149 q = 1) (hb : d69644 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53149, d69644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d53149, d69644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d53150 q = 1) (hb : d69645 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53150, d69645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d53150, d69645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d53151 q = 1) (hb : d73280 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53151, d73280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53151, d73280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro7365 (p : Pattern) (ha : d53171 p = 1) (hb : d69646 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53073 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5112 q = 1) (hb : d53144 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5112, d53144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro233 q ha hb
    | true =>
      simp only [d5112, d53144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53075 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d53145 q = 1) (hb : d69635 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53145, d69635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d53145, d69635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1820 q = 1) (hb : d53146 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1820, d53146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro219 q ha hb
    | true =>
      simp only [d1820, d53146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1821 q = 1) (hb : d53147 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1821, d53147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1821, d53147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53148 q = 1) (hb : d69636 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53148, d69636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53148, d69636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d53169 q = 1) (hb : d69644 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53169, d69644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53169, d69644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53170 q = 1) (hb : d69645 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53170, d69645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53170, d69645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53171 q = 1) (hb : d69646 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53171, d69646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53171, d69646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7366 (p : Pattern) (ha : d53252 p = 1) (hb : d69656 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53239 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5170 q = 1) (hb : d53240 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5170, d53240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro239 q ha hb
    | true =>
      simp only [d5170, d53240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53245 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d53246 q = 1) (hb : d69652 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53246, d69652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d53246, d69652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1964 q = 1) (hb : d53247 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1964, d53247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro240 q ha hb
    | true =>
      simp only [d1964, d53247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1965 q = 1) (hb : d53248 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1965, d53248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1965, d53248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53249 q = 1) (hb : d69653 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53249, d69653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53249, d69653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d53250 q = 1) (hb : d69654 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53250, d69654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53250, d69654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53251 q = 1) (hb : d69655 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53251, d69655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53251, d69655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53252 q = 1) (hb : d69656 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53252, d69656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53252, d69656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7367 (p : Pattern) (ha : d58533 p = 1) (hb : d73286 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53083 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53152 q = 1) (hb : d73281 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53152, d73281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7363 q ha hb
    | true =>
      simp only [d53152, d73281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7364 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d58522 q = 1) (hb : d73282 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58522, d73282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58522, d73282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d58523 q = 1) (hb : d73283 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58523, d73283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58523, d73283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h5 (q : Pattern) (ha : d58524 q = 1) (hb : d73284 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58524, d73284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58524, d73284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53172 q = 1) (hb : d69647 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53172, d69647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d53172, d69647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7365 q ha hb
  have h7 (q : Pattern) (ha : d58525 q = 1) (hb : d69648 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58525, d69648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58525, d69648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h8 (q : Pattern) (ha : d58526 q = 1) (hb : d69649 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58526, d69649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d58526, d69649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h9 (q : Pattern) (ha : d58527 q = 1) (hb : d69650 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58527, d69650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d58527, d69650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h10 (q : Pattern) (ha : d58528 q = 1) (hb : d73285 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58528, d73285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58528, d73285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53253 q = 1) (hb : d69657 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53253, d69657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d53253, d69657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7366 q ha hb
  have h12 (q : Pattern) (ha : d58529 q = 1) (hb : d69658 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58529, d69658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d58529, d69658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h13 (q : Pattern) (ha : d58530 q = 1) (hb : d69659 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58530, d69659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d58530, d69659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h14 (q : Pattern) (ha : d58531 q = 1) (hb : d69660 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58531, d69660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d58531, d69660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h15 (q : Pattern) (ha : d58532 q = 1) (hb : d69661 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58532, d69661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d58532, d69661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h16 (q : Pattern) (ha : d58533 q = 1) (hb : d73286 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58533, d73286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d58533, d73286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro7368 (p : Pattern) (ha : d58539 p = 1) (hb : d73292 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58534 q = 1) (hb : d73287 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58534, d73287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58534, d73287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7367 q ha hb
  have h2 (q : Pattern) (ha : d58535 q = 1) (hb : d73288 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58535, d73288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58535, d73288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d58536 q = 1) (hb : d73289 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58536, d73289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58536, d73289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58537 q = 1) (hb : d73290 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58537, d73290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58537, d73290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58538 q = 1) (hb : d73291 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58538, d73291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58538, d73291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58539 q = 1) (hb : d73292 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58539, d73292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58539, d73292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7369 (p : Pattern) (ha : d53448 p = 1) (hb : d73299 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53412 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53421 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53381 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5215 q = 1) (hb : d53441 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5215, d53441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro305 q ha hb
    | true =>
      simp only [d5215, d53441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d53442 q = 1) (hb : d69673 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53442, d69673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d53442, d69673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d2275 q = 1) (hb : d53443 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2275, d53443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro275 q ha hb
    | true =>
      simp only [d2275, d53443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2276 q = 1) (hb : d53444 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2276, d53444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2276, d53444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53445 q = 1) (hb : d69674 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53445, d69674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53445, d69674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d53446 q = 1) (hb : d73297 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53446, d73297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d53446, d73297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53447 q = 1) (hb : d73298 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53447, d73298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53447, d73298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d53448 q = 1) (hb : d73299 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53448, d73299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53448, d73299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro7370 (p : Pattern) (ha : d53468 p = 1) (hb : d73300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53412 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53421 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53381 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5215 q = 1) (hb : d53441 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5215, d53441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro305 q ha hb
    | true =>
      simp only [d5215, d53441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53442 q = 1) (hb : d69673 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53442, d69673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d53442, d69673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2275 q = 1) (hb : d53443 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2275, d53443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro275 q ha hb
    | true =>
      simp only [d2275, d53443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2276 q = 1) (hb : d53444 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2276, d53444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2276, d53444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d53445 q = 1) (hb : d69674 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53445, d69674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53445, d69674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d53446 q = 1) (hb : d73297 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53446, d73297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53446, d73297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53447 q = 1) (hb : d73298 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53447, d73298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53447, d73298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d53454 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d53459 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53394 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d5229 q = 1) (hb : d53461 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5229, d53461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro292 q ha hb
    | true =>
      simp only [d5229, d53461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d53396 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d53462 q = 1) (hb : d69678 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53462, d69678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d53462, d69678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d2298 q = 1) (hb : d53463 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2298, d53463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro278 q ha hb
    | true =>
      simp only [d2298, d53463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h19 (q : Pattern) (ha : d2299 q = 1) (hb : d53464 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2299, d53464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d2299, d53464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h20 (q : Pattern) (ha : d53465 q = 1) (hb : d69679 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53465, d69679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d53465, d69679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d53466 q = 1) (hb : d69687 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53466, d69687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d53466, d69687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d53467 q = 1) (hb : d69688 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53467, d69688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d53467, d69688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d53468 q = 1) (hb : d73300 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53468, d73300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53468, d73300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro7371 (p : Pattern) (ha : d53488 p = 1) (hb : d69689 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53394 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5229 q = 1) (hb : d53461 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5229, d53461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro292 q ha hb
    | true =>
      simp only [d5229, d53461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53396 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d53462 q = 1) (hb : d69678 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53462, d69678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d53462, d69678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d2298 q = 1) (hb : d53463 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2298, d53463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro278 q ha hb
    | true =>
      simp only [d2298, d53463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2299 q = 1) (hb : d53464 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2299, d53464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2299, d53464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53465 q = 1) (hb : d69679 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53465, d69679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53465, d69679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d53486 q = 1) (hb : d69687 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53486, d69687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53486, d69687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53487 q = 1) (hb : d69688 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53487, d69688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53487, d69688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53488 q = 1) (hb : d69689 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53488, d69689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53488, d69689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7372 (p : Pattern) (ha : d53569 p = 1) (hb : d69699 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53556 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5283 q = 1) (hb : d53557 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5283, d53557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro298 q ha hb
    | true =>
      simp only [d5283, d53557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53562 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d53563 q = 1) (hb : d69695 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53563, d69695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d53563, d69695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d2442 q = 1) (hb : d53564 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2442, d53564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro299 q ha hb
    | true =>
      simp only [d2442, d53564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2443 q = 1) (hb : d53565 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2443, d53565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2443, d53565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53566 q = 1) (hb : d69696 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53566, d69696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53566, d69696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d53567 q = 1) (hb : d69697 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53567, d69697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53567, d69697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53568 q = 1) (hb : d69698 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53568, d69698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53568, d69698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53569 q = 1) (hb : d69699 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53569, d69699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53569, d69699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7373 (p : Pattern) (ha : d58555 p = 1) (hb : d73306 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53404 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53469 q = 1) (hb : d73301 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53469, d73301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7369 q ha hb
    | true =>
      simp only [d53469, d73301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7370 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d58544 q = 1) (hb : d73302 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58544, d73302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58544, d73302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d58545 q = 1) (hb : d73303 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58545, d73303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58545, d73303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h5 (q : Pattern) (ha : d58546 q = 1) (hb : d73304 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58546, d73304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58546, d73304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53489 q = 1) (hb : d69690 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53489, d69690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d53489, d69690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7371 q ha hb
  have h7 (q : Pattern) (ha : d58547 q = 1) (hb : d69691 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58547, d69691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58547, d69691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h8 (q : Pattern) (ha : d58548 q = 1) (hb : d69692 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58548, d69692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d58548, d69692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h9 (q : Pattern) (ha : d58549 q = 1) (hb : d69693 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58549, d69693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d58549, d69693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h10 (q : Pattern) (ha : d58550 q = 1) (hb : d73305 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58550, d73305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58550, d73305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53570 q = 1) (hb : d69700 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53570, d69700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d53570, d69700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7372 q ha hb
  have h12 (q : Pattern) (ha : d58551 q = 1) (hb : d69701 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58551, d69701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d58551, d69701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h13 (q : Pattern) (ha : d58552 q = 1) (hb : d69702 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58552, d69702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d58552, d69702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h14 (q : Pattern) (ha : d58553 q = 1) (hb : d69703 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58553, d69703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d58553, d69703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h15 (q : Pattern) (ha : d58554 q = 1) (hb : d69704 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58554, d69704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d58554, d69704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h16 (q : Pattern) (ha : d58555 q = 1) (hb : d73306 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58555, d73306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d58555, d73306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro7374 (p : Pattern) (ha : d58561 p = 1) (hb : d73312 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58556 q = 1) (hb : d73307 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58556, d73307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58556, d73307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7373 q ha hb
  have h2 (q : Pattern) (ha : d58557 q = 1) (hb : d73308 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58557, d73308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58557, d73308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d58558 q = 1) (hb : d73309 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58558, d73309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58558, d73309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58559 q = 1) (hb : d73310 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58559, d73310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58559, d73310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58560 q = 1) (hb : d73311 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58560, d73311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58560, d73311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58561 q = 1) (hb : d73312 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58561, d73312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58561, d73312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7375 (p : Pattern) (ha : d58567 p = 1) (hb : d73318 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d58480 q = 1) (hb : d73239 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58480, d73239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7344 q ha hb
    | true =>
      simp only [d58480, d73239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7350 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d58499 q = 1) (hb : d73256 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58499, d73256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d58499, d73256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7356 q ha hb
  have h3 (q : Pattern) (ha : d58500 q = 1) (hb : d73257 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d58500, d73257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58500, d73257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58519 q = 1) (hb : d73274 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58519, d73274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d58519, d73274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7362 q ha hb
  have h5 (q : Pattern) (ha : d58520 q = 1) (hb : d73275 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d58520, d73275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d58520, d73275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58521 q = 1) (hb : d73276 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d58521, d73276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58521, d73276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d58540 q = 1) (hb : d73293 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58540, d73293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d58540, d73293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7368 q ha hb
  have h8 (q : Pattern) (ha : d58541 q = 1) (hb : d73294 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d58541, d73294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d58541, d73294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d58542 q = 1) (hb : d73295 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d58542, d73295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d58542, d73295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d58543 q = 1) (hb : d73296 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d58543, d73296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58543, d73296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d58562 q = 1) (hb : d73313 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58562, d73313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d58562, d73313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7374 q ha hb
  have h12 (q : Pattern) (ha : d58563 q = 1) (hb : d73314 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d58563, d73314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d58563, d73314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d58564 q = 1) (hb : d73315 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d58564, d73315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d58564, d73315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d58565 q = 1) (hb : d73316 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d58565, d73316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d58565, d73316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d58566 q = 1) (hb : d73317 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d58566, d73317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d58566, d73317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d58567 q = 1) (hb : d73318 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d58567, d73318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d58567, d73318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro7376 (p : Pattern) (ha : d58573 p = 1) (hb : d73324 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58568 q = 1) (hb : d73319 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d58568, d73319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7375 q ha hb
    | true =>
      simp only [d58568, d73319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d58569 q = 1) (hb : d73320 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d58569, d73320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58569, d73320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d58570 q = 1) (hb : d73321 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d58570, d73321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58570, d73321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d58571 q = 1) (hb : d73322 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d58571, d73322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58571, d73322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d58572 q = 1) (hb : d73323 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d58572, d73323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58572, d73323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d58573 q = 1) (hb : d73324 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d58573, d73324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58573, d73324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro7377 (p : Pattern) (ha : d58579 p = 1) (hb : d73330 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58574 q = 1) (hb : d73325 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d58574, d73325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7376 q ha hb
    | true =>
      simp only [d58574, d73325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d58575 q = 1) (hb : d73326 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d58575, d73326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58575, d73326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d58576 q = 1) (hb : d73327 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d58576, d73327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58576, d73327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d58577 q = 1) (hb : d73328 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d58577, d73328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58577, d73328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d58578 q = 1) (hb : d73329 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d58578, d73329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58578, d73329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d58579 q = 1) (hb : d73330 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d58579, d73330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58579, d73330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro7378 (p : Pattern) (ha : d58585 p = 1) (hb : d73336 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58580 q = 1) (hb : d73331 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d58580, d73331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7377 q ha hb
    | true =>
      simp only [d58580, d73331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d58581 q = 1) (hb : d73332 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d58581, d73332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58581, d73332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d58582 q = 1) (hb : d73333 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d58582, d73333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58582, d73333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d58583 q = 1) (hb : d73334 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d58583, d73334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58583, d73334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d58584 q = 1) (hb : d73335 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d58584, d73335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58584, d73335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d58585 q = 1) (hb : d73336 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d58585, d73336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58585, d73336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro7379 (p : Pattern) (ha : d58591 p = 1) (hb : d73342 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58586 q = 1) (hb : d73337 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d58586, d73337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7378 q ha hb
    | true =>
      simp only [d58586, d73337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d58587 q = 1) (hb : d73338 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d58587, d73338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58587, d73338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d58588 q = 1) (hb : d73339 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d58588, d73339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58588, d73339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d58589 q = 1) (hb : d73340 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d58589, d73340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58589, d73340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d58590 q = 1) (hb : d73341 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d58590, d73341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58590, d73341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d58591 q = 1) (hb : d73342 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d58591, d73342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58591, d73342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro7380 (p : Pattern) (ha : d58597 p = 1) (hb : d73348 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58592 q = 1) (hb : d73343 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d58592, d73343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7379 q ha hb
    | true =>
      simp only [d58592, d73343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d58593 q = 1) (hb : d73344 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d58593, d73344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58593, d73344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d58594 q = 1) (hb : d73345 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d58594, d73345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58594, d73345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d58595 q = 1) (hb : d73346 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d58595, d73346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58595, d73346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d58596 q = 1) (hb : d73347 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d58596, d73347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58596, d73347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d58597 q = 1) (hb : d73348 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d58597, d73348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58597, d73348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro7381 (p : Pattern) (ha : d58603 p = 1) (hb : d73354 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58598 q = 1) (hb : d73349 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d58598, d73349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7380 q ha hb
    | true =>
      simp only [d58598, d73349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d58599 q = 1) (hb : d73350 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d58599, d73350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58599, d73350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d58600 q = 1) (hb : d73351 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d58600, d73351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58600, d73351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d58601 q = 1) (hb : d73352 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d58601, d73352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58601, d73352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d58602 q = 1) (hb : d73353 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d58602, d73353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58602, d73353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d58603 q = 1) (hb : d73354 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d58603, d73354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58603, d73354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro7382 (p : Pattern) (ha : d58609 p = 1) (hb : d73360 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58604 q = 1) (hb : d73355 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d58604, d73355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7381 q ha hb
    | true =>
      simp only [d58604, d73355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d58605 q = 1) (hb : d73356 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d58605, d73356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58605, d73356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d58606 q = 1) (hb : d73357 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d58606, d73357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58606, d73357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d58607 q = 1) (hb : d73358 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d58607, d73358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58607, d73358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d58608 q = 1) (hb : d73359 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d58608, d73359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58608, d73359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d58609 q = 1) (hb : d73360 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d58609, d73360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58609, d73360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro7383 (p : Pattern) (ha : d0 p = 1) (hb : d73191 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro7384 (p : Pattern) (ha : d0 p = 1) (hb : d58609 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58609 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro7385 (p : Pattern) (ha : d0 p = 1) (hb : d58743 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58743 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro7386 (p : Pattern) (ha : d4644 p = 1) (hb : d68223 p = 1) : d68744 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4639 q = 1) (hb : d68222 q = 1) : d68739 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d4639, d68739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7272 q ha hb
    | true =>
      simp only [d4639, d68739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4640 q = 1) (hb : d68222 q = 1) : d68740 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d4640, d68740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4640, d68740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4641 q = 1) (hb : d68223 q = 1) : d68741 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d4641, d68223, d68741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4641, d68223, d68741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d68223 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d4642 q = 1) (hb : d68223 q = 1) : d68742 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d4642, d68742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4642, d68742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4643 q = 1) (hb : d68223 q = 1) : d68743 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d4643, d68743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4643, d68743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d4644 q = 1) (hb : d68223 q = 1) : d68744 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d4644, d68744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4644, d68744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro7387 (p : Pattern) (ha : d4650 p = 1) (hb : d68223 p = 1) : d68750 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68223 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4645 q = 1) (hb : d68223 q = 1) : d68745 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d4645, d68745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7386 q ha hb
    | true =>
      simp only [d4645, d68745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4646 q = 1) (hb : d68223 q = 1) : d68746 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d4646, d68746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4646, d68746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4647 q = 1) (hb : d68223 q = 1) : d68747 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d4647, d68747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4647, d68747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4648 q = 1) (hb : d68223 q = 1) : d68748 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d4648, d68748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4648, d68748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4649 q = 1) (hb : d68223 q = 1) : d68749 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d4649, d68749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4649, d68749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4650 q = 1) (hb : d68223 q = 1) : d68750 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d4650, d68750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4650, d68750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7388 (p : Pattern) (ha : d52013 p = 1) (hb : d68542 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d157 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30 q ha hb
    | true =>
      simp only [d157, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4335 q = 1) (hb : d52009 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d52009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4335, d52009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d52010 q = 1) (hb : d67611 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52010, d67611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d52010, d67611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d52011 q = 1) (hb : d68540 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52011, d68540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d52011, d68540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d52012 q = 1) (hb : d68541 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52012, d68541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52012, d68541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52013 q = 1) (hb : d68542 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52013, d68542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52013, d68542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7389 (p : Pattern) (ha : d52029 p = 1) (hb : d68543 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d157 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30 q ha hb
    | true =>
      simp only [d157, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4335 q = 1) (hb : d52009 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d52009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4335, d52009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d52010 q = 1) (hb : d67611 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52010, d67611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52010, d67611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d52011 q = 1) (hb : d68540 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52011, d68540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52011, d68540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52012 q = 1) (hb : d68541 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52012, d68541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52012, d68541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52018 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52022 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d204 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22 q ha hb
    | true =>
      simp only [d204, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4340 q = 1) (hb : d52025 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d52025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4340, d52025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d52026 q = 1) (hb : d67615 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52026, d67615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d52026, d67615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d52027 q = 1) (hb : d67623 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52027, d67623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d52027, d67623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d52028 q = 1) (hb : d67624 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52028, d67624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d52028, d67624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d52029 q = 1) (hb : d68543 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52029, d68543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d52029, d68543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro7390 (p : Pattern) (ha : d52073 p = 1) (hb : d68549 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51966 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52030 q = 1) (hb : d68544 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52030, d68544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7388 q ha hb
    | true =>
      simp only [d52030, d68544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7389 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52032 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d52033 q = 1) (hb : d68545 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52033, d68545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d52033, d68545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d52034 q = 1) (hb : d68546 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52034, d68546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52034, d68546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d52035 q = 1) (hb : d68547 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52035, d68547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52035, d68547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52039 q = 1) (hb : d67626 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52039, d67626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52039, d67626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6786 q ha hb
  have h8 (q : Pattern) (ha : d52040 q = 1) (hb : d67627 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52040, d67627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52040, d67627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d52041 q = 1) (hb : d67628 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52041, d67628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d52041, d67628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d52042 q = 1) (hb : d67629 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52042, d67629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d52042, d67629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d52043 q = 1) (hb : d68548 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52043, d68548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52043, d68548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d52068 q = 1) (hb : d67635 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52068, d67635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52068, d67635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6787 q ha hb
  have h13 (q : Pattern) (ha : d52069 q = 1) (hb : d67636 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52069, d67636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d52069, d67636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d52070 q = 1) (hb : d67637 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52070, d67637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d52070, d67637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d52071 q = 1) (hb : d67638 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52071, d67638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d52071, d67638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h16 (q : Pattern) (ha : d52072 q = 1) (hb : d67639 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52072, d67639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d52072, d67639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d52073 q = 1) (hb : d68549 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d52073, d68549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d52073, d68549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro7391 (p : Pattern) (ha : d52143 p = 1) (hb : d68557 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52099 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52105 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d337 q = 1) (hb : d52136 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d337, d52136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53 q ha hb
    | true =>
      simp only [d337, d52136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4371 q = 1) (hb : d52137 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4371, d52137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4371, d52137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52139 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d52140 q = 1) (hb : d67646 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52140, d67646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d52140, d67646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d52141 q = 1) (hb : d68555 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52141, d68555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d52141, d68555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d52142 q = 1) (hb : d68556 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52142, d68556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52142, d68556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52143 q = 1) (hb : d68557 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52143, d68557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52143, d68557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7392 (p : Pattern) (ha : d52161 p = 1) (hb : d68558 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52105 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d337 q = 1) (hb : d52136 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d337, d52136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53 q ha hb
    | true =>
      simp only [d337, d52136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4371 q = 1) (hb : d52137 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4371, d52137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4371, d52137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52139 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d52140 q = 1) (hb : d67646 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52140, d67646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52140, d67646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d52141 q = 1) (hb : d68555 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52141, d68555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52141, d68555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52142 q = 1) (hb : d68556 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52142, d68556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52142, d68556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52148 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52152 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d386 q = 1) (hb : d52154 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d386, d52154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45 q ha hb
    | true =>
      simp only [d386, d52154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4376 q = 1) (hb : d52155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4376, d52155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4376, d52155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52157 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d52158 q = 1) (hb : d67650 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52158, d67650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d52158, d67650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d52159 q = 1) (hb : d67658 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52159, d67658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d52159, d67658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d52160 q = 1) (hb : d67659 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52160, d67659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d52160, d67659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d52161 q = 1) (hb : d68558 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52161, d68558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d52161, d68558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro7393 (p : Pattern) (ha : d52215 p = 1) (hb : d68571 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52093 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52162 q = 1) (hb : d68559 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52162, d68559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7391 q ha hb
    | true =>
      simp only [d52162, d68559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7392 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52164 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d52165 q = 1) (hb : d68560 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52165, d68560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d52165, d68560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d52166 q = 1) (hb : d68561 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52166, d68561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52166, d68561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d52167 q = 1) (hb : d68562 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52167, d68562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52167, d68562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52171 q = 1) (hb : d67661 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52171, d67661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52171, d67661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6791 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d52174 q = 1) (hb : d68563 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52174, d68563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52174, d68563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d52175 q = 1) (hb : d68564 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52175, d68564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d52175, d68564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d52176 q = 1) (hb : d68565 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52176, d68565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d52176, d68565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d52177 q = 1) (hb : d68566 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52177, d68566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52177, d68566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d52204 q = 1) (hb : d67670 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52204, d67670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52204, d67670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6792 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d52211 q = 1) (hb : d68567 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52211, d68567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d52211, d68567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d52212 q = 1) (hb : d68568 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52212, d68568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d52212, d68568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d52213 q = 1) (hb : d68569 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52213, d68569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d52213, d68569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d52214 q = 1) (hb : d68570 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52214, d68570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d52214, d68570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d52215 q = 1) (hb : d68571 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d52215, d68571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d52215, d68571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro7394 (p : Pattern) (ha : d52221 p = 1) (hb : d68577 p = 1) : d0 p = 1 := by
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
  have h5 (q : Pattern) (ha : d52074 q = 1) (hb : d68550 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d52074, d68550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52074, d68550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7390 q ha hb
  have h6 (q : Pattern) (ha : d52075 q = 1) (hb : d68551 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d52075, d68551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52075, d68551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52076 q = 1) (hb : d68552 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d52076, d68552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52076, d68552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52077 q = 1) (hb : d68553 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d52077, d68553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52077, d68553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d52078 q = 1) (hb : d68554 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d52078, d68554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52078, d68554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52216 q = 1) (hb : d68572 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d52216, d68572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52216, d68572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7393 q ha hb
  have h11 (q : Pattern) (ha : d52217 q = 1) (hb : d68573 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d52217, d68573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52217, d68573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d52218 q = 1) (hb : d68574 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d52218, d68574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52218, d68574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d52219 q = 1) (hb : d68575 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d52219, d68575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52219, d68575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d52220 q = 1) (hb : d68576 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d52220, d68576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52220, d68576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d52221 q = 1) (hb : d68577 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d52221, d68577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d52221, d68577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro7395 (p : Pattern) (ha : d52315 p = 1) (hb : d68580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52265 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52274 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d561 q = 1) (hb : d52308 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d561, d52308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91 q ha hb
    | true =>
      simp only [d561, d52308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52239 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4408 q = 1) (hb : d52309 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4408, d52309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4408, d52309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52311 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d52312 q = 1) (hb : d67682 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52312, d67682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d52312, d67682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d52313 q = 1) (hb : d68578 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52313, d68578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d52313, d68578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d52314 q = 1) (hb : d68579 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52314, d68579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52314, d68579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52315 q = 1) (hb : d68580 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52315, d68580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52315, d68580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7396 (p : Pattern) (ha : d52335 p = 1) (hb : d68581 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52265 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52274 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d561 q = 1) (hb : d52308 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d561, d52308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91 q ha hb
    | true =>
      simp only [d561, d52308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52239 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4408 q = 1) (hb : d52309 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4408, d52309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4408, d52309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52311 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d52312 q = 1) (hb : d67682 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52312, d67682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52312, d67682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d52313 q = 1) (hb : d68578 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52313, d68578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52313, d68578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52314 q = 1) (hb : d68579 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52314, d68579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52314, d68579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52321 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52326 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d621 q = 1) (hb : d52328 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d621, d52328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79 q ha hb
    | true =>
      simp only [d621, d52328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d52249 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4413 q = 1) (hb : d52329 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4413, d52329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4413, d52329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52331 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d52332 q = 1) (hb : d67686 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52332, d67686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d52332, d67686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d52333 q = 1) (hb : d67694 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52333, d67694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d52333, d67694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d52334 q = 1) (hb : d67695 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52334, d67695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d52334, d67695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d52335 q = 1) (hb : d68581 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52335, d68581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d52335, d68581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro7397 (p : Pattern) (ha : d52419 p = 1) (hb : d68594 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52257 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52336 q = 1) (hb : d68582 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52336, d68582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7395 q ha hb
    | true =>
      simp only [d52336, d68582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7396 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52349 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d52350 q = 1) (hb : d68583 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52350, d68583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d52350, d68583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d52351 q = 1) (hb : d68584 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52351, d68584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52351, d68584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d52352 q = 1) (hb : d68585 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52352, d68585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52352, d68585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52356 q = 1) (hb : d67697 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52356, d67697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52356, d67697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6797 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52358 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d52359 q = 1) (hb : d68586 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52359, d68586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52359, d68586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d52360 q = 1) (hb : d68587 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52360, d68587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d52360, d68587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d52361 q = 1) (hb : d68588 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52361, d68588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d52361, d68588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d52362 q = 1) (hb : d68589 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52362, d68589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52362, d68589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d52407 q = 1) (hb : d67706 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52407, d67706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52407, d67706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6798 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52414 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d52415 q = 1) (hb : d68590 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52415, d68590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d52415, d68590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d52416 q = 1) (hb : d68591 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52416, d68591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d52416, d68591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d52417 q = 1) (hb : d68592 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52417, d68592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d52417, d68592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d52418 q = 1) (hb : d68593 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52418, d68593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d52418, d68593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d52419 q = 1) (hb : d68594 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d52419, d68594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d52419, d68594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro7398 (p : Pattern) (ha : d52425 p = 1) (hb : d68600 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52420 q = 1) (hb : d68595 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d52420, d68595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52420, d68595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7397 q ha hb
  have h2 (q : Pattern) (ha : d52421 q = 1) (hb : d68596 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d52421, d68596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52421, d68596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52422 q = 1) (hb : d68597 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d52422, d68597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52422, d68597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52423 q = 1) (hb : d68598 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d52423, d68598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52423, d68598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52424 q = 1) (hb : d68599 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d52424, d68599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52424, d68599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52425 q = 1) (hb : d68600 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d52425, d68600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52425, d68600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7399 (p : Pattern) (ha : d52536 p = 1) (hb : d68604 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52487 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52496 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d852 q = 1) (hb : d52529 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d852, d52529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro138 q ha hb
    | true =>
      simp only [d852, d52529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52461 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4446 q = 1) (hb : d52530 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4446, d52530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4446, d52530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52532 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d52533 q = 1) (hb : d67719 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52533, d67719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d52533, d67719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d52534 q = 1) (hb : d68602 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52534, d68602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d52534, d68602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d52535 q = 1) (hb : d68603 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52535, d68603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52535, d68603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52536 q = 1) (hb : d68604 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52536, d68604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52536, d68604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7400 (p : Pattern) (ha : d52556 p = 1) (hb : d68605 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52496 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d852 q = 1) (hb : d52529 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d852, d52529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro138 q ha hb
    | true =>
      simp only [d852, d52529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52461 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4446 q = 1) (hb : d52530 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4446, d52530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4446, d52530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52532 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d52533 q = 1) (hb : d67719 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52533, d67719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52533, d67719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d52534 q = 1) (hb : d68602 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52534, d68602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52534, d68602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52535 q = 1) (hb : d68603 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52535, d68603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52535, d68603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52542 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52547 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d927 q = 1) (hb : d52549 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d927, d52549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro125 q ha hb
    | true =>
      simp only [d927, d52549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro109 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d52471 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4451 q = 1) (hb : d52550 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4451, d52550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4451, d52550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52552 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d52553 q = 1) (hb : d67723 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52553, d67723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d52553, d67723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d52554 q = 1) (hb : d67731 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52554, d67731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d52554, d67731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d52555 q = 1) (hb : d67732 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52555, d67732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d52555, d67732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d52556 q = 1) (hb : d68605 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52556, d68605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d52556, d68605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro7401 (p : Pattern) (ha : d52656 p = 1) (hb : d68618 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52479 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52557 q = 1) (hb : d68606 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52557, d68606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7399 q ha hb
    | true =>
      simp only [d52557, d68606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7400 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52570 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d52571 q = 1) (hb : d68607 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52571, d68607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d52571, d68607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d52572 q = 1) (hb : d68608 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52572, d68608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52572, d68608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d52573 q = 1) (hb : d68609 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52573, d68609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52573, d68609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52577 q = 1) (hb : d67734 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52577, d67734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52577, d67734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6803 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52579 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d52580 q = 1) (hb : d68610 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52580, d68610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52580, d68610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d52581 q = 1) (hb : d68611 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52581, d68611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d52581, d68611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d52582 q = 1) (hb : d68612 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52582, d68612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d52582, d68612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d52583 q = 1) (hb : d68613 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52583, d68613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52583, d68613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d52644 q = 1) (hb : d67743 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52644, d67743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52644, d67743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6804 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52651 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d52652 q = 1) (hb : d68614 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52652, d68614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d52652, d68614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d52653 q = 1) (hb : d68615 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52653, d68615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d52653, d68615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d52654 q = 1) (hb : d68616 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52654, d68616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d52654, d68616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d52655 q = 1) (hb : d68617 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52655, d68617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d52655, d68617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d52656 q = 1) (hb : d68618 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d52656, d68618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d52656, d68618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro7402 (p : Pattern) (ha : d52662 p = 1) (hb : d68624 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52657 q = 1) (hb : d68619 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d52657, d68619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52657, d68619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7401 q ha hb
  have h2 (q : Pattern) (ha : d52658 q = 1) (hb : d68620 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d52658, d68620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52658, d68620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52659 q = 1) (hb : d68621 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d52659, d68621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52659, d68621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52660 q = 1) (hb : d68622 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d52660, d68622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52660, d68622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52661 q = 1) (hb : d68623 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d52661, d68623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52661, d68623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52662 q = 1) (hb : d68624 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d52662, d68624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52662, d68624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7403 (p : Pattern) (ha : d52816 p = 1) (hb : d68629 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52770 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52779 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1228 q = 1) (hb : d52809 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1228, d52809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro190 q ha hb
    | true =>
      simp only [d1228, d52809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro158 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52744 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4485 q = 1) (hb : d52810 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4485, d52810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4485, d52810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52812 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d52813 q = 1) (hb : d67757 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52813, d67757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d52813, d67757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d52814 q = 1) (hb : d68627 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52814, d68627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d52814, d68627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d52815 q = 1) (hb : d68628 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52815, d68628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52815, d68628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52816 q = 1) (hb : d68629 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52816, d68629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52816, d68629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7404 (p : Pattern) (ha : d52836 p = 1) (hb : d68630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52770 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52779 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1228 q = 1) (hb : d52809 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1228, d52809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro190 q ha hb
    | true =>
      simp only [d1228, d52809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro158 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52744 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4485 q = 1) (hb : d52810 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4485, d52810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4485, d52810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52812 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d52813 q = 1) (hb : d67757 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52813, d67757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52813, d67757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d52814 q = 1) (hb : d68627 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52814, d68627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52814, d68627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52815 q = 1) (hb : d68628 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52815, d68628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52815, d68628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52822 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52827 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d1338 q = 1) (hb : d52829 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1338, d52829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro177 q ha hb
    | true =>
      simp only [d1338, d52829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro161 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d52754 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4490 q = 1) (hb : d52830 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4490, d52830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4490, d52830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52832 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d52833 q = 1) (hb : d67761 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52833, d67761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d52833, d67761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d52834 q = 1) (hb : d67769 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52834, d67769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d52834, d67769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d52835 q = 1) (hb : d67770 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52835, d67770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d52835, d67770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d52836 q = 1) (hb : d68630 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52836, d68630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d52836, d68630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro7405 (p : Pattern) (ha : d52950 p = 1) (hb : d68643 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52837 q = 1) (hb : d68631 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52837, d68631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7403 q ha hb
    | true =>
      simp only [d52837, d68631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7404 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52850 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d52851 q = 1) (hb : d68632 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52851, d68632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d52851, d68632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d52852 q = 1) (hb : d68633 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52852, d68633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52852, d68633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d52853 q = 1) (hb : d68634 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52853, d68634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52853, d68634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52857 q = 1) (hb : d67772 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52857, d67772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52857, d67772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6809 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52859 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d52860 q = 1) (hb : d68635 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52860, d68635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52860, d68635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d52861 q = 1) (hb : d68636 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52861, d68636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d52861, d68636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d52862 q = 1) (hb : d68637 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52862, d68637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d52862, d68637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d52863 q = 1) (hb : d68638 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52863, d68638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52863, d68638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d52938 q = 1) (hb : d67781 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52938, d67781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52938, d67781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6810 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52945 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d52946 q = 1) (hb : d68639 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52946, d68639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d52946, d68639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d52947 q = 1) (hb : d68640 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52947, d68640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d52947, d68640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d52948 q = 1) (hb : d68641 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52948, d68641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d52948, d68641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d52949 q = 1) (hb : d68642 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52949, d68642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d52949, d68642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d52950 q = 1) (hb : d68643 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d52950, d68643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d52950, d68643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro7406 (p : Pattern) (ha : d52956 p = 1) (hb : d68649 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52951 q = 1) (hb : d68644 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d52951, d68644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52951, d68644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7405 q ha hb
  have h2 (q : Pattern) (ha : d52952 q = 1) (hb : d68645 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d52952, d68645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52952, d68645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52953 q = 1) (hb : d68646 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d52953, d68646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52953, d68646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52954 q = 1) (hb : d68647 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d52954, d68647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52954, d68647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52955 q = 1) (hb : d68648 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d52955, d68648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52955, d68648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52956 q = 1) (hb : d68649 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d52956, d68649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52956, d68649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7407 (p : Pattern) (ha : d53131 p = 1) (hb : d68655 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53091 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53100 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1683 q = 1) (hb : d53124 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1683, d53124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro246 q ha hb
    | true =>
      simp only [d1683, d53124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro216 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53065 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4525 q = 1) (hb : d53125 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4525, d53125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4525, d53125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53127 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d53128 q = 1) (hb : d67796 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53128, d67796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d53128, d67796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d53129 q = 1) (hb : d68653 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53129, d68653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d53129, d68653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53130 q = 1) (hb : d68654 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53130, d68654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53130, d68654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53131 q = 1) (hb : d68655 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53131, d68655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53131, d68655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7408 (p : Pattern) (ha : d53151 p = 1) (hb : d68656 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53091 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53100 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1683 q = 1) (hb : d53124 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1683, d53124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro246 q ha hb
    | true =>
      simp only [d1683, d53124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro216 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53065 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4525 q = 1) (hb : d53125 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4525, d53125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4525, d53125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53127 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d53128 q = 1) (hb : d67796 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53128, d67796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d53128, d67796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d53129 q = 1) (hb : d68653 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53129, d68653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53129, d68653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53130 q = 1) (hb : d68654 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53130, d68654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53130, d68654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53137 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53142 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d1815 q = 1) (hb : d53144 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1815, d53144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro233 q ha hb
    | true =>
      simp only [d1815, d53144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro219 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d53075 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4530 q = 1) (hb : d53145 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4530, d53145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4530, d53145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53147 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d53148 q = 1) (hb : d67800 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53148, d67800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d53148, d67800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d53149 q = 1) (hb : d67808 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53149, d67808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d53149, d67808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d53150 q = 1) (hb : d67809 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53150, d67809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d53150, d67809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d53151 q = 1) (hb : d68656 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53151, d68656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53151, d68656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro7409 (p : Pattern) (ha : d53265 p = 1) (hb : d68669 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53083 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53152 q = 1) (hb : d68657 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53152, d68657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7407 q ha hb
    | true =>
      simp only [d53152, d68657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7408 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53165 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d53166 q = 1) (hb : d68658 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53166, d68658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53166, d68658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53167 q = 1) (hb : d68659 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53167, d68659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53167, d68659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d53168 q = 1) (hb : d68660 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53168, d68660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53168, d68660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53172 q = 1) (hb : d67811 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53172, d67811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d53172, d67811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6815 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53174 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d53175 q = 1) (hb : d68661 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53175, d68661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53175, d68661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d53176 q = 1) (hb : d68662 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53176, d68662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53176, d68662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d53177 q = 1) (hb : d68663 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53177, d68663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53177, d68663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d53178 q = 1) (hb : d68664 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53178, d68664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53178, d68664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d53253 q = 1) (hb : d67820 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53253, d67820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d53253, d67820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6816 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53260 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d53261 q = 1) (hb : d68665 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53261, d68665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53261, d68665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d53262 q = 1) (hb : d68666 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53262, d68666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53262, d68666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d53263 q = 1) (hb : d68667 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53263, d68667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d53263, d68667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d53264 q = 1) (hb : d68668 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53264, d68668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d53264, d68668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d53265 q = 1) (hb : d68669 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53265, d68669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53265, d68669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro7410 (p : Pattern) (ha : d53271 p = 1) (hb : d68675 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53266 q = 1) (hb : d68670 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53266, d68670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53266, d68670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7409 q ha hb
  have h2 (q : Pattern) (ha : d53267 q = 1) (hb : d68671 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53267, d68671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53267, d68671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53268 q = 1) (hb : d68672 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53268, d68672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53268, d68672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53269 q = 1) (hb : d68673 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53269, d68673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53269, d68673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53270 q = 1) (hb : d68674 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53270, d68674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53270, d68674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53271 q = 1) (hb : d68675 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53271, d68675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53271, d68675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7411 (p : Pattern) (ha : d53448 p = 1) (hb : d68682 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53412 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53421 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2162 q = 1) (hb : d53441 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2162, d53441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro305 q ha hb
    | true =>
      simp only [d2162, d53441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro275 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4566 q = 1) (hb : d53442 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4566, d53442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4566, d53442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53444 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d53445 q = 1) (hb : d67836 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53445, d67836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d53445, d67836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d53446 q = 1) (hb : d68680 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53446, d68680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d53446, d68680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53447 q = 1) (hb : d68681 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53447, d68681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53447, d68681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53448 q = 1) (hb : d68682 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53448, d68682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53448, d68682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7412 (p : Pattern) (ha : d53468 p = 1) (hb : d68683 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53412 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53421 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2162 q = 1) (hb : d53441 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2162, d53441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro305 q ha hb
    | true =>
      simp only [d2162, d53441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro275 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4566 q = 1) (hb : d53442 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4566, d53442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4566, d53442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53444 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d53445 q = 1) (hb : d67836 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53445, d67836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d53445, d67836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d53446 q = 1) (hb : d68680 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53446, d68680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53446, d68680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53447 q = 1) (hb : d68681 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53447, d68681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53447, d68681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53454 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53459 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d2293 q = 1) (hb : d53461 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2293, d53461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro292 q ha hb
    | true =>
      simp only [d2293, d53461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro278 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d53396 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4571 q = 1) (hb : d53462 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4571, d53462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4571, d53462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53464 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d53465 q = 1) (hb : d67840 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53465, d67840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d53465, d67840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d53466 q = 1) (hb : d67848 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53466, d67848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d53466, d67848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d53467 q = 1) (hb : d67849 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53467, d67849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d53467, d67849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d53468 q = 1) (hb : d68683 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53468, d68683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53468, d68683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro7413 (p : Pattern) (ha : d53582 p = 1) (hb : d68696 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53404 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53469 q = 1) (hb : d68684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53469, d68684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7411 q ha hb
    | true =>
      simp only [d53469, d68684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7412 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53482 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d53483 q = 1) (hb : d68685 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53483, d68685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53483, d68685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53484 q = 1) (hb : d68686 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53484, d68686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53484, d68686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d53485 q = 1) (hb : d68687 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53485, d68687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53485, d68687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53489 q = 1) (hb : d67851 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53489, d67851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d53489, d67851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6821 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53491 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d53492 q = 1) (hb : d68688 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53492, d68688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53492, d68688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d53493 q = 1) (hb : d68689 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53493, d68689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53493, d68689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d53494 q = 1) (hb : d68690 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53494, d68690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53494, d68690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d53495 q = 1) (hb : d68691 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53495, d68691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53495, d68691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d53570 q = 1) (hb : d67860 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53570, d67860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d53570, d67860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6822 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53577 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d53578 q = 1) (hb : d68692 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53578, d68692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53578, d68692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d53579 q = 1) (hb : d68693 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53579, d68693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53579, d68693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d53580 q = 1) (hb : d68694 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53580, d68694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d53580, d68694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d53581 q = 1) (hb : d68695 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53581, d68695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d53581, d68695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d53582 q = 1) (hb : d68696 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53582, d68696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53582, d68696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro7414 (p : Pattern) (ha : d53588 p = 1) (hb : d68702 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53583 q = 1) (hb : d68697 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53583, d68697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53583, d68697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7413 q ha hb
  have h2 (q : Pattern) (ha : d53584 q = 1) (hb : d68698 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53584, d68698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53584, d68698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53585 q = 1) (hb : d68699 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53585, d68699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53585, d68699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53586 q = 1) (hb : d68700 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53586, d68700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53586, d68700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53587 q = 1) (hb : d68701 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53587, d68701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53587, d68701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53588 q = 1) (hb : d68702 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53588, d68702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53588, d68702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7415 (p : Pattern) (ha : d53594 p = 1) (hb : d68708 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d52426 q = 1) (hb : d68601 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d52426, d68601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7394 q ha hb
    | true =>
      simp only [d52426, d68601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7398 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52663 q = 1) (hb : d68625 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d52663, d68625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52663, d68625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7402 q ha hb
  have h3 (q : Pattern) (ha : d52664 q = 1) (hb : d68626 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d52664, d68626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d52664, d68626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52957 q = 1) (hb : d68650 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d52957, d68650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52957, d68650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7406 q ha hb
  have h5 (q : Pattern) (ha : d52958 q = 1) (hb : d68651 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d52958, d68651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52958, d68651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52959 q = 1) (hb : d68652 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d52959, d68652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52959, d68652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53272 q = 1) (hb : d68676 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53272, d68676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53272, d68676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7410 q ha hb
  have h8 (q : Pattern) (ha : d53273 q = 1) (hb : d68677 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53273, d68677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53273, d68677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53274 q = 1) (hb : d68678 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53274, d68678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53274, d68678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53275 q = 1) (hb : d68679 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d53275, d68679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53275, d68679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53589 q = 1) (hb : d68703 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53589, d68703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53589, d68703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7414 q ha hb
  have h12 (q : Pattern) (ha : d53590 q = 1) (hb : d68704 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53590, d68704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53590, d68704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d53591 q = 1) (hb : d68705 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53591, d68705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53591, d68705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d53592 q = 1) (hb : d68706 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d53592, d68706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53592, d68706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d53593 q = 1) (hb : d68707 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d53593, d68707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53593, d68707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d53594 q = 1) (hb : d68708 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d53594, d68708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53594, d68708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro7416 (p : Pattern) (ha : d53600 p = 1) (hb : d68714 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53595 q = 1) (hb : d68709 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d53595, d68709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7415 q ha hb
    | true =>
      simp only [d53595, d68709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53596 q = 1) (hb : d68710 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d53596, d68710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53596, d68710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d53597 q = 1) (hb : d68711 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d53597, d68711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53597, d68711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53598 q = 1) (hb : d68712 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d53598, d68712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53598, d68712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53599 q = 1) (hb : d68713 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d53599, d68713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53599, d68713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53600 q = 1) (hb : d68714 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d53600, d68714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53600, d68714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro7417 (p : Pattern) (ha : d53606 p = 1) (hb : d68720 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53601 q = 1) (hb : d68715 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d53601, d68715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7416 q ha hb
    | true =>
      simp only [d53601, d68715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53602 q = 1) (hb : d68716 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d53602, d68716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53602, d68716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d53603 q = 1) (hb : d68717 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d53603, d68717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53603, d68717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53604 q = 1) (hb : d68718 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d53604, d68718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53604, d68718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53605 q = 1) (hb : d68719 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d53605, d68719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53605, d68719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53606 q = 1) (hb : d68720 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d53606, d68720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53606, d68720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro7418 (p : Pattern) (ha : d53612 p = 1) (hb : d68726 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53607 q = 1) (hb : d68721 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d53607, d68721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7417 q ha hb
    | true =>
      simp only [d53607, d68721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53608 q = 1) (hb : d68722 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d53608, d68722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53608, d68722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d53609 q = 1) (hb : d68723 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d53609, d68723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53609, d68723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53610 q = 1) (hb : d68724 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d53610, d68724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53610, d68724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53611 q = 1) (hb : d68725 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d53611, d68725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53611, d68725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53612 q = 1) (hb : d68726 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d53612, d68726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53612, d68726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro7419 (p : Pattern) (ha : d53618 p = 1) (hb : d68732 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53613 q = 1) (hb : d68727 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d53613, d68727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7418 q ha hb
    | true =>
      simp only [d53613, d68727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53614 q = 1) (hb : d68728 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d53614, d68728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53614, d68728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d53615 q = 1) (hb : d68729 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d53615, d68729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53615, d68729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53616 q = 1) (hb : d68730 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d53616, d68730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53616, d68730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53617 q = 1) (hb : d68731 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d53617, d68731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53617, d68731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53618 q = 1) (hb : d68732 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d53618, d68732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53618, d68732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro7420 (p : Pattern) (ha : d53624 p = 1) (hb : d68738 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53619 q = 1) (hb : d68733 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d53619, d68733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7419 q ha hb
    | true =>
      simp only [d53619, d68733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53620 q = 1) (hb : d68734 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d53620, d68734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53620, d68734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d53621 q = 1) (hb : d68735 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d53621, d68735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53621, d68735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53622 q = 1) (hb : d68736 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d53622, d68736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53622, d68736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53623 q = 1) (hb : d68737 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d53623, d68737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53623, d68737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53624 q = 1) (hb : d68738 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d53624, d68738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53624, d68738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro7421 (p : Pattern) (ha : d53630 p = 1) (hb : d68744 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53625 q = 1) (hb : d68739 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d53625, d68739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7420 q ha hb
    | true =>
      simp only [d53625, d68739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53626 q = 1) (hb : d68740 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d53626, d68740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53626, d68740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d53627 q = 1) (hb : d68741 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d53627, d68741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53627, d68741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53628 q = 1) (hb : d68742 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d53628, d68742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53628, d68742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53629 q = 1) (hb : d68743 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d53629, d68743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53629, d68743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53630 q = 1) (hb : d68744 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d53630, d68744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53630, d68744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro7422 (p : Pattern) (ha : d53636 p = 1) (hb : d68750 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53631 q = 1) (hb : d68745 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d53631, d68745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7421 q ha hb
    | true =>
      simp only [d53631, d68745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53632 q = 1) (hb : d68746 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d53632, d68746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53632, d68746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d53633 q = 1) (hb : d68747 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d53633, d68747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53633, d68747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53634 q = 1) (hb : d68748 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d53634, d68748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53634, d68748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53635 q = 1) (hb : d68749 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d53635, d68749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53635, d68749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53636 q = 1) (hb : d68750 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d53636, d68750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53636, d68750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro7423 (p : Pattern) (ha : d0 p = 1) (hb : d68223 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68223 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro7424 (p : Pattern) (ha : d0 p = 1) (hb : d53636 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53636 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro7425 (p : Pattern) (ha : d0 p = 1) (hb : d51865 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51865 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro7426 (p : Pattern) (ha : d4339 p = 1) (hb : d75630 p = 1) : d76455 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d157 q = 1) (hb : d75629 q = 1) : d4737 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d75629, d4737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4469 q ha hb
    | true =>
      simp only [d157, d75629, d4737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4335 q = 1) (hb : d75630 q = 1) : d5350 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d75630, d5350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4335, d75630, d5350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44 q = 1) (hb : d75630 q = 1) : d44 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d4336 q = 1) (hb : d75630 q = 1) : d76452 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d76452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4336, d76452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4337 q = 1) (hb : d75630 q = 1) : d76453 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4337, d76453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4337, d76453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4338 q = 1) (hb : d75630 q = 1) : d76454 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4338, d76454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4338, d76454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4339 q = 1) (hb : d75630 q = 1) : d76455 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4339, d76455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4339, d76455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro7427 (p : Pattern) (ha : d4344 p = 1) (hb : d75630 p = 1) : d76459 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d157 q = 1) (hb : d75629 q = 1) : d4737 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d75629, d4737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4469 q ha hb
    | true =>
      simp only [d157, d75629, d4737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4335 q = 1) (hb : d75630 q = 1) : d5350 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d75630, d5350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4335, d75630, d5350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44 q = 1) (hb : d75630 q = 1) : d44 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d4336 q = 1) (hb : d75630 q = 1) : d76452 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d76452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4336, d76452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4337 q = 1) (hb : d75630 q = 1) : d76453 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4337, d76453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4337, d76453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4338 q = 1) (hb : d75630 q = 1) : d76454 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4338, d76454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4338, d76454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d49 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d204 q = 1) (hb : d75629 q = 1) : d5356 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d75629, d5356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4465 q ha hb
    | true =>
      simp only [d204, d75629, d5356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d4340 q = 1) (hb : d75630 q = 1) : d5357 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d75630, d5357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4340, d75630, d5357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h12 (q : Pattern) (ha : d51 q = 1) (hb : d75630 q = 1) : d51 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4341 q = 1) (hb : d75630 q = 1) : d76456 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d76456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4341, d76456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d4342 q = 1) (hb : d75630 q = 1) : d76457 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4342, d76457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4342, d76457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d4343 q = 1) (hb : d75630 q = 1) : d76458 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4343, d76458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4343, d76458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d4344 q = 1) (hb : d75630 q = 1) : d76459 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4344, d76459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4344, d76459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro7428 (p : Pattern) (ha : d4349 p = 1) (hb : d75630 p = 1) : d76464 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d49 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d204 q = 1) (hb : d75629 q = 1) : d5356 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d75629, d5356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4465 q ha hb
    | true =>
      simp only [d204, d75629, d5356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4340 q = 1) (hb : d75630 q = 1) : d5357 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d75630, d5357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4340, d75630, d5357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51 q = 1) (hb : d75630 q = 1) : d51 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d4341 q = 1) (hb : d75630 q = 1) : d76456 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d76456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4341, d76456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4342 q = 1) (hb : d75630 q = 1) : d76457 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4342, d76457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4342, d76457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4343 q = 1) (hb : d75630 q = 1) : d76458 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4343, d76458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4343, d76458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4349 q = 1) (hb : d75630 q = 1) : d76464 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4349, d76464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4349, d76464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro7429 (p : Pattern) (ha : d4359 p = 1) (hb : d75630 p = 1) : d76473 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d83 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d244 q = 1) (hb : d75629 q = 1) : d5378 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d244, d75629, d5378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4467 q ha hb
    | true =>
      simp only [d244, d75629, d5378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4355 q = 1) (hb : d75630 q = 1) : d5379 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4355, d75630, d5379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4355, d75630, d5379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85 q = 1) (hb : d75630 q = 1) : d85 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d4356 q = 1) (hb : d75630 q = 1) : d76470 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4356, d76470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4356, d76470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4357 q = 1) (hb : d75630 q = 1) : d76471 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4357, d76471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4357, d76471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4358 q = 1) (hb : d75630 q = 1) : d76472 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4358, d76472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4358, d76472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4359 q = 1) (hb : d75630 q = 1) : d76473 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4359, d76473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4359, d76473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro7430 (p : Pattern) (ha : d4365 p = 1) (hb : d75630 p = 1) : d76479 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4345 q = 1) (hb : d75630 q = 1) : d76460 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4345, d76460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7426 q ha hb
    | true =>
      simp only [d4345, d76460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7427 q ha hb
  have h2 (q : Pattern) (ha : d4346 q = 1) (hb : d75630 q = 1) : d76461 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4346, d76461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4346, d76461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4347 q = 1) (hb : d75630 q = 1) : d76462 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4347, d76462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4347, d76462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4348 q = 1) (hb : d75630 q = 1) : d76463 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4348, d76463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4348, d76463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4350 q = 1) (hb : d75630 q = 1) : d76465 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4350, d76465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4350, d76465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7428 q ha hb
  have h6 (q : Pattern) (ha : d4351 q = 1) (hb : d75630 q = 1) : d76466 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4351, d76466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4351, d76466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d4352 q = 1) (hb : d75630 q = 1) : d76467 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4352, d76467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4352, d76467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d4353 q = 1) (hb : d75630 q = 1) : d76468 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4353, d76468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4353, d76468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d4354 q = 1) (hb : d75630 q = 1) : d76469 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4354, d76469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4354, d76469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4360 q = 1) (hb : d75630 q = 1) : d76474 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4360, d76474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4360, d76474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7429 q ha hb
  have h11 (q : Pattern) (ha : d4361 q = 1) (hb : d75630 q = 1) : d76475 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4361, d76475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4361, d76475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4362 q = 1) (hb : d75630 q = 1) : d76476 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4362, d76476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4362, d76476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d4363 q = 1) (hb : d75630 q = 1) : d76477 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4363, d76477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4363, d76477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d4364 q = 1) (hb : d75630 q = 1) : d76478 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4364, d76478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4364, d76478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d4365 q = 1) (hb : d75630 q = 1) : d76479 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d4365, d76479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4365, d76479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro7431 (p : Pattern) (ha : d336 p = 1) (hb : d70145 p = 1) : d5921 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d332 q = 1) : d332 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d152 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d333 q = 1) (hb : d70145 q = 1) : d5918 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333, d70145, d5918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d333, d70145, d5918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d334 q = 1) (hb : d70145 q = 1) : d5919 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334, d5919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d334, d5919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d335 q = 1) (hb : d70145 q = 1) : d5920 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d335, d5920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d335, d5920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d336 q = 1) (hb : d70145 q = 1) : d5921 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d336, d5921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d336, d5921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7432 (p : Pattern) (ha : d4375 p = 1) (hb : d75630 p = 1) : d76490 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d156 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d337 q = 1) (hb : d75629 q = 1) : d76485 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d337, d75629, d76485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7431 q ha hb
    | true =>
      simp only [d337, d75629, d76485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4371 q = 1) (hb : d75630 q = 1) : d76486 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4371, d75630, d76486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4371, d75630, d76486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d370 q = 1) (hb : d75629 q = 1) : d4737 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d370, d75629, d4737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4469 q ha hb
    | true =>
      simp only [d370, d75629, d4737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d371 q = 1) (hb : d75630 q = 1) : d5350 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371, d75630, d5350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d371, d75630, d5350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d4372 q = 1) (hb : d75630 q = 1) : d76487 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4372, d76487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4372, d76487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4373 q = 1) (hb : d75630 q = 1) : d76488 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4373, d76488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4373, d76488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4374 q = 1) (hb : d75630 q = 1) : d76489 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4374, d76489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4374, d76489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4375 q = 1) (hb : d75630 q = 1) : d76490 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4375, d76490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4375, d76490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7433 (p : Pattern) (ha : d385 p = 1) (hb : d70145 p = 1) : d5942 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d332 q = 1) : d332 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d152 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d333 q = 1) (hb : d70145 q = 1) : d5918 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333, d70145, d5918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333, d70145, d5918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d334 q = 1) (hb : d70145 q = 1) : d5919 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334, d5919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d334, d5919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d335 q = 1) (hb : d70145 q = 1) : d5920 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d335, d5920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d335, d5920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d385 q = 1) (hb : d70145 q = 1) : d5942 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d385, d5942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d385, d5942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro7434 (p : Pattern) (ha : d4380 p = 1) (hb : d75630 p = 1) : d76496 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d156 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d337 q = 1) (hb : d75629 q = 1) : d76485 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d337, d75629, d76485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7431 q ha hb
    | true =>
      simp only [d337, d75629, d76485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4371 q = 1) (hb : d75630 q = 1) : d76486 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4371, d75630, d76486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4371, d75630, d76486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d370 q = 1) (hb : d75629 q = 1) : d4737 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d370, d75629, d4737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4469 q ha hb
    | true =>
      simp only [d370, d75629, d4737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d371 q = 1) (hb : d75630 q = 1) : d5350 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371, d75630, d5350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d371, d75630, d5350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d4372 q = 1) (hb : d75630 q = 1) : d76487 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4372, d76487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4372, d76487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4373 q = 1) (hb : d75630 q = 1) : d76488 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4373, d76488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4373, d76488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4374 q = 1) (hb : d75630 q = 1) : d76489 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4374, d76489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4374, d76489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d203 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d386 q = 1) (hb : d75629 q = 1) : d76491 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d386, d75629, d76491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7433 q ha hb
    | true =>
      simp only [d386, d75629, d76491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d4376 q = 1) (hb : d75630 q = 1) : d76492 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4376, d75630, d76492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4376, d75630, d76492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h13 (q : Pattern) (ha : d390 q = 1) (hb : d75629 q = 1) : d5356 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d390, d75629, d5356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4465 q ha hb
    | true =>
      simp only [d390, d75629, d5356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d391 q = 1) (hb : d75630 q = 1) : d5357 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d391, d75630, d5357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d391, d75630, d5357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h15 (q : Pattern) (ha : d4377 q = 1) (hb : d75630 q = 1) : d76493 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4377, d76493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4377, d76493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d4378 q = 1) (hb : d75630 q = 1) : d76494 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4378, d76494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4378, d76494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d4379 q = 1) (hb : d75630 q = 1) : d76495 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4379, d76495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4379, d76495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d4380 q = 1) (hb : d75630 q = 1) : d76496 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4380, d76496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4380, d76496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro7435 (p : Pattern) (ha : d4385 p = 1) (hb : d75630 p = 1) : d76501 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d203 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d386 q = 1) (hb : d75629 q = 1) : d76491 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d386, d75629, d76491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7433 q ha hb
    | true =>
      simp only [d386, d75629, d76491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4376 q = 1) (hb : d75630 q = 1) : d76492 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4376, d75630, d76492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4376, d75630, d76492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d390 q = 1) (hb : d75629 q = 1) : d5356 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d390, d75629, d5356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4465 q ha hb
    | true =>
      simp only [d390, d75629, d5356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d391 q = 1) (hb : d75630 q = 1) : d5357 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d391, d75630, d5357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d391, d75630, d5357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d4377 q = 1) (hb : d75630 q = 1) : d76493 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4377, d76493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4377, d76493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4378 q = 1) (hb : d75630 q = 1) : d76494 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4378, d76494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4378, d76494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4379 q = 1) (hb : d75630 q = 1) : d76495 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4379, d76495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4379, d76495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4385 q = 1) (hb : d75630 q = 1) : d76501 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4385, d76501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4385, d76501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7436 (p : Pattern) (ha : d429 p = 1) (hb : d70145 p = 1) : d5968 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d425 q = 1) : d425 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d239 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d426 q = 1) (hb : d70145 q = 1) : d5965 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d426, d70145, d5965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d426, d70145, d5965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d427 q = 1) (hb : d70145 q = 1) : d5966 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d427, d5966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d427, d5966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d428 q = 1) (hb : d70145 q = 1) : d5967 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d428, d5967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d428, d5967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d429 q = 1) (hb : d70145 q = 1) : d5968 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d429, d5968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d429, d5968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro7437 (p : Pattern) (ha : d4395 p = 1) (hb : d75630 p = 1) : d76512 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d243 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d430 q = 1) (hb : d75629 q = 1) : d76507 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d430, d75629, d76507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7436 q ha hb
    | true =>
      simp only [d430, d75629, d76507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4391 q = 1) (hb : d75630 q = 1) : d76508 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4391, d75630, d76508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4391, d75630, d76508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d451 q = 1) (hb : d75629 q = 1) : d5378 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d451, d75629, d5378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4467 q ha hb
    | true =>
      simp only [d451, d75629, d5378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d452 q = 1) (hb : d75630 q = 1) : d5379 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d452, d75630, d5379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d452, d75630, d5379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d4392 q = 1) (hb : d75630 q = 1) : d76509 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4392, d76509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4392, d76509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4393 q = 1) (hb : d75630 q = 1) : d76510 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4393, d76510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4393, d76510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4394 q = 1) (hb : d75630 q = 1) : d76511 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4394, d76511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4394, d76511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4395 q = 1) (hb : d75630 q = 1) : d76512 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4395, d76512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4395, d76512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7438 (p : Pattern) (ha : d4401 p = 1) (hb : d75630 p = 1) : d76518 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4381 q = 1) (hb : d75630 q = 1) : d76497 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4381, d76497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7432 q ha hb
    | true =>
      simp only [d4381, d76497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7434 q ha hb
  have h2 (q : Pattern) (ha : d4382 q = 1) (hb : d75630 q = 1) : d76498 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4382, d76498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4382, d76498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4383 q = 1) (hb : d75630 q = 1) : d76499 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4383, d76499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4383, d76499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4384 q = 1) (hb : d75630 q = 1) : d76500 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4384, d76500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4384, d76500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4386 q = 1) (hb : d75630 q = 1) : d76502 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4386, d76502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4386, d76502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7435 q ha hb
  have h6 (q : Pattern) (ha : d4387 q = 1) (hb : d75630 q = 1) : d76503 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4387, d76503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4387, d76503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d4388 q = 1) (hb : d75630 q = 1) : d76504 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4388, d76504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4388, d76504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d4389 q = 1) (hb : d75630 q = 1) : d76505 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4389, d76505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4389, d76505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d4390 q = 1) (hb : d75630 q = 1) : d76506 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4390, d76506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4390, d76506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4396 q = 1) (hb : d75630 q = 1) : d76513 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4396, d76513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4396, d76513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7437 q ha hb
  have h11 (q : Pattern) (ha : d4397 q = 1) (hb : d75630 q = 1) : d76514 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4397, d76514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4397, d76514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4398 q = 1) (hb : d75630 q = 1) : d76515 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4398, d76515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4398, d76515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d4399 q = 1) (hb : d75630 q = 1) : d76516 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4399, d76516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4399, d76516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d4400 q = 1) (hb : d75630 q = 1) : d76517 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4400, d76517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4400, d76517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d4401 q = 1) (hb : d75630 q = 1) : d76518 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d4401, d76518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4401, d76518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro7439 (p : Pattern) (ha : d4407 p = 1) (hb : d75630 p = 1) : d76524 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d75630 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4366 q = 1) (hb : d75630 q = 1) : d76480 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d4366, d76480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4366, d76480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7430 q ha hb
  have h3 (q : Pattern) (ha : d4367 q = 1) (hb : d75630 q = 1) : d76481 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d4367, d76481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4367, d76481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4368 q = 1) (hb : d75630 q = 1) : d76482 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d4368, d76482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4368, d76482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4369 q = 1) (hb : d75630 q = 1) : d76483 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d4369, d76483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4369, d76483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4370 q = 1) (hb : d75630 q = 1) : d76484 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d4370, d76484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4370, d76484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4402 q = 1) (hb : d75630 q = 1) : d76519 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d4402, d76519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4402, d76519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7438 q ha hb
  have h8 (q : Pattern) (ha : d4403 q = 1) (hb : d75630 q = 1) : d76520 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d4403, d76520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4403, d76520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4404 q = 1) (hb : d75630 q = 1) : d76521 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d4404, d76521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4404, d76521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4405 q = 1) (hb : d75630 q = 1) : d76522 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d4405, d76522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4405, d76522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4406 q = 1) (hb : d75630 q = 1) : d76523 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d4406, d76523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4406, d76523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4407 q = 1) (hb : d75630 q = 1) : d76524 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d4407, d76524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4407, d76524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro7440 (p : Pattern) (ha : d560 p = 1) (hb : d70145 p = 1) : d6024 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d556 q = 1) : d556 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d479 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d557 q = 1) (hb : d70145 q = 1) : d6021 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d557, d70145, d6021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d557, d70145, d6021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d558 q = 1) (hb : d70145 q = 1) : d6022 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d558, d6022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d558, d6022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d559 q = 1) (hb : d70145 q = 1) : d6023 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d559, d6023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d559, d6023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d560 q = 1) (hb : d70145 q = 1) : d6024 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d560, d6024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d560, d6024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7441 (p : Pattern) (ha : d4412 p = 1) (hb : d75630 p = 1) : d76530 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d487 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d561 q = 1) (hb : d75629 q = 1) : d76525 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d561, d75629, d76525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7440 q ha hb
    | true =>
      simp only [d561, d75629, d76525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4408 q = 1) (hb : d75630 q = 1) : d76526 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4408, d75630, d76526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4408, d75630, d76526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d603 q = 1) (hb : d75629 q = 1) : d5400 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d603, d75629, d5400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4480 q ha hb
    | true =>
      simp only [d603, d75629, d5400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d604 q = 1) (hb : d75630 q = 1) : d5401 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d604, d75630, d5401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d604, d75630, d5401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d4409 q = 1) (hb : d75630 q = 1) : d76527 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4409, d76527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4409, d76527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4410 q = 1) (hb : d75630 q = 1) : d76528 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4410, d76528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4410, d76528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4411 q = 1) (hb : d75630 q = 1) : d76529 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4411, d76529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4411, d76529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4412 q = 1) (hb : d75630 q = 1) : d76530 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4412, d76530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4412, d76530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7442 (p : Pattern) (ha : d620 p = 1) (hb : d70145 p = 1) : d6045 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d556 q = 1) : d556 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d479 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d557 q = 1) (hb : d70145 q = 1) : d6021 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d557, d70145, d6021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d557, d70145, d6021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d558 q = 1) (hb : d70145 q = 1) : d6022 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d558, d6022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d558, d6022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d559 q = 1) (hb : d70145 q = 1) : d6023 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d559, d6023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d559, d6023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d620 q = 1) (hb : d70145 q = 1) : d6045 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d620, d6045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d620, d6045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro7443 (p : Pattern) (ha : d4417 p = 1) (hb : d75630 p = 1) : d76536 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d487 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d561 q = 1) (hb : d75629 q = 1) : d76525 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d561, d75629, d76525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7440 q ha hb
    | true =>
      simp only [d561, d75629, d76525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4408 q = 1) (hb : d75630 q = 1) : d76526 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4408, d75630, d76526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4408, d75630, d76526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d603 q = 1) (hb : d75629 q = 1) : d5400 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d603, d75629, d5400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4480 q ha hb
    | true =>
      simp only [d603, d75629, d5400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d604 q = 1) (hb : d75630 q = 1) : d5401 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d604, d75630, d5401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d604, d75630, d5401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d4409 q = 1) (hb : d75630 q = 1) : d76527 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4409, d76527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4409, d76527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4410 q = 1) (hb : d75630 q = 1) : d76528 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4410, d76528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4410, d76528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4411 q = 1) (hb : d75630 q = 1) : d76529 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4411, d76529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4411, d76529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d500 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d621 q = 1) (hb : d75629 q = 1) : d76531 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d621, d75629, d76531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7442 q ha hb
    | true =>
      simp only [d621, d75629, d76531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d4413 q = 1) (hb : d75630 q = 1) : d76532 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4413, d75630, d76532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4413, d75630, d76532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h13 (q : Pattern) (ha : d626 q = 1) (hb : d75629 q = 1) : d5407 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d626, d75629, d5407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4476 q ha hb
    | true =>
      simp only [d626, d75629, d5407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d627 q = 1) (hb : d75630 q = 1) : d5408 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d627, d75630, d5408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d627, d75630, d5408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h15 (q : Pattern) (ha : d4414 q = 1) (hb : d75630 q = 1) : d76533 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4414, d76533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4414, d76533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d4415 q = 1) (hb : d75630 q = 1) : d76534 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4415, d76534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4415, d76534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d4416 q = 1) (hb : d75630 q = 1) : d76535 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4416, d76535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4416, d76535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d4417 q = 1) (hb : d75630 q = 1) : d76536 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4417, d76536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4417, d76536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro7444 (p : Pattern) (ha : d4422 p = 1) (hb : d75630 p = 1) : d76541 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d500 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d621 q = 1) (hb : d75629 q = 1) : d76531 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d621, d75629, d76531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7442 q ha hb
    | true =>
      simp only [d621, d75629, d76531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4413 q = 1) (hb : d75630 q = 1) : d76532 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4413, d75630, d76532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4413, d75630, d76532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d626 q = 1) (hb : d75629 q = 1) : d5407 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d626, d75629, d5407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4476 q ha hb
    | true =>
      simp only [d626, d75629, d5407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d627 q = 1) (hb : d75630 q = 1) : d5408 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d627, d75630, d5408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d627, d75630, d5408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d4414 q = 1) (hb : d75630 q = 1) : d76533 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4414, d76533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4414, d76533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4415 q = 1) (hb : d75630 q = 1) : d76534 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4415, d76534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4415, d76534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4416 q = 1) (hb : d75630 q = 1) : d76535 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4416, d76535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4416, d76535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4422 q = 1) (hb : d75630 q = 1) : d76541 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4422, d76541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4422, d76541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7445 (p : Pattern) (ha : d681 p = 1) (hb : d70145 p = 1) : d6077 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d672 q = 1) : d672 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d677 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d678 q = 1) (hb : d70145 q = 1) : d6074 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d678, d70145, d6074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d678, d70145, d6074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d679 q = 1) (hb : d70145 q = 1) : d6075 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d679, d6075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d679, d6075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d680 q = 1) (hb : d70145 q = 1) : d6076 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d680, d6076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d680, d6076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d681 q = 1) (hb : d70145 q = 1) : d6077 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d681, d6077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d681, d6077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro7446 (p : Pattern) (ha : d4432 p = 1) (hb : d75630 p = 1) : d76552 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d689 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d690 q = 1) (hb : d75629 q = 1) : d76547 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d690, d75629, d76547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7445 q ha hb
    | true =>
      simp only [d690, d75629, d76547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4428 q = 1) (hb : d75630 q = 1) : d76548 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4428, d75630, d76548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4428, d75630, d76548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d720 q = 1) (hb : d75629 q = 1) : d5429 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d720, d75629, d5429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4478 q ha hb
    | true =>
      simp only [d720, d75629, d5429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d721 q = 1) (hb : d75630 q = 1) : d5430 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d721, d75630, d5430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d721, d75630, d5430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d4429 q = 1) (hb : d75630 q = 1) : d76549 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4429, d76549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4429, d76549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4430 q = 1) (hb : d75630 q = 1) : d76550 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4430, d76550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4430, d76550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4431 q = 1) (hb : d75630 q = 1) : d76551 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4431, d76551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4431, d76551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4432 q = 1) (hb : d75630 q = 1) : d76552 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4432, d76552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4432, d76552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7447 (p : Pattern) (ha : d4438 p = 1) (hb : d75630 p = 1) : d76558 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4418 q = 1) (hb : d75630 q = 1) : d76537 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4418, d76537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7441 q ha hb
    | true =>
      simp only [d4418, d76537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7443 q ha hb
  have h2 (q : Pattern) (ha : d4419 q = 1) (hb : d75630 q = 1) : d76538 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4419, d76538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4419, d76538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4420 q = 1) (hb : d75630 q = 1) : d76539 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4420, d76539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4420, d76539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4421 q = 1) (hb : d75630 q = 1) : d76540 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4421, d76540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4421, d76540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4423 q = 1) (hb : d75630 q = 1) : d76542 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4423, d76542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4423, d76542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7444 q ha hb
  have h6 (q : Pattern) (ha : d4424 q = 1) (hb : d75630 q = 1) : d76543 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4424, d76543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4424, d76543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d4425 q = 1) (hb : d75630 q = 1) : d76544 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4425, d76544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4425, d76544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d4426 q = 1) (hb : d75630 q = 1) : d76545 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4426, d76545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4426, d76545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d4427 q = 1) (hb : d75630 q = 1) : d76546 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4427, d76546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4427, d76546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4433 q = 1) (hb : d75630 q = 1) : d76553 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4433, d76553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4433, d76553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7446 q ha hb
  have h11 (q : Pattern) (ha : d4434 q = 1) (hb : d75630 q = 1) : d76554 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4434, d76554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4434, d76554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4435 q = 1) (hb : d75630 q = 1) : d76555 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4435, d76555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4435, d76555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d4436 q = 1) (hb : d75630 q = 1) : d76556 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4436, d76556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4436, d76556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d4437 q = 1) (hb : d75630 q = 1) : d76557 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4437, d76557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4437, d76557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d4438 q = 1) (hb : d75630 q = 1) : d76558 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d4438, d76558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4438, d76558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro7448 (p : Pattern) (ha : d4444 p = 1) (hb : d75630 p = 1) : d76564 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4439 q = 1) (hb : d75630 q = 1) : d76559 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d4439, d76559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4439, d76559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7447 q ha hb
  have h2 (q : Pattern) (ha : d4440 q = 1) (hb : d75630 q = 1) : d76560 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d4440, d76560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4440, d76560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4441 q = 1) (hb : d75630 q = 1) : d76561 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d4441, d76561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4441, d76561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4442 q = 1) (hb : d75630 q = 1) : d76562 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d4442, d76562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4442, d76562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4443 q = 1) (hb : d75630 q = 1) : d76563 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d4443, d76563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4443, d76563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4444 q = 1) (hb : d75630 q = 1) : d76564 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d4444, d76564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4444, d76564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7449 (p : Pattern) (ha : d851 p = 1) (hb : d70145 p = 1) : d6152 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d847 q = 1) : d847 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d771 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d848 q = 1) (hb : d70145 q = 1) : d6149 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d848, d70145, d6149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d848, d70145, d6149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d849 q = 1) (hb : d70145 q = 1) : d6150 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d849, d6150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d849, d6150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d850 q = 1) (hb : d70145 q = 1) : d6151 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d850, d6151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d850, d6151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d851 q = 1) (hb : d70145 q = 1) : d6152 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d851, d6152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d851, d6152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7450 (p : Pattern) (ha : d4450 p = 1) (hb : d75630 p = 1) : d76571 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d779 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d852 q = 1) (hb : d75629 q = 1) : d76566 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d852, d75629, d76566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7449 q ha hb
    | true =>
      simp only [d852, d75629, d76566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4446 q = 1) (hb : d75630 q = 1) : d76567 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4446, d75630, d76567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4446, d75630, d76567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d909 q = 1) (hb : d75629 q = 1) : d6160 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d909, d75629, d6160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4491 q ha hb
    | true =>
      simp only [d909, d75629, d6160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d910 q = 1) (hb : d75630 q = 1) : d6161 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d910, d75630, d6161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d910, d75630, d6161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d4447 q = 1) (hb : d75630 q = 1) : d76568 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4447, d76568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4447, d76568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4448 q = 1) (hb : d75630 q = 1) : d76569 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4448, d76569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4448, d76569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4449 q = 1) (hb : d75630 q = 1) : d76570 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4449, d76570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4449, d76570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4450 q = 1) (hb : d75630 q = 1) : d76571 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4450, d76571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4450, d76571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7451 (p : Pattern) (ha : d926 p = 1) (hb : d70145 p = 1) : d6175 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d847 q = 1) : d847 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d771 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d848 q = 1) (hb : d70145 q = 1) : d6149 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d848, d70145, d6149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d848, d70145, d6149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d849 q = 1) (hb : d70145 q = 1) : d6150 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d849, d6150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d849, d6150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d850 q = 1) (hb : d70145 q = 1) : d6151 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d850, d6151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d850, d6151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d926 q = 1) (hb : d70145 q = 1) : d6175 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d926, d6175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d926, d6175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro7452 (p : Pattern) (ha : d4455 p = 1) (hb : d75630 p = 1) : d76577 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d779 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d852 q = 1) (hb : d75629 q = 1) : d76566 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d852, d75629, d76566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7449 q ha hb
    | true =>
      simp only [d852, d75629, d76566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4446 q = 1) (hb : d75630 q = 1) : d76567 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4446, d75630, d76567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4446, d75630, d76567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d909 q = 1) (hb : d75629 q = 1) : d6160 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d909, d75629, d6160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4491 q ha hb
    | true =>
      simp only [d909, d75629, d6160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d910 q = 1) (hb : d75630 q = 1) : d6161 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d910, d75630, d6161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d910, d75630, d6161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d4447 q = 1) (hb : d75630 q = 1) : d76568 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4447, d76568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4447, d76568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4448 q = 1) (hb : d75630 q = 1) : d76569 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4448, d76569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4448, d76569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4449 q = 1) (hb : d75630 q = 1) : d76570 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4449, d76570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4449, d76570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d792 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d927 q = 1) (hb : d75629 q = 1) : d76572 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d927, d75629, d76572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7451 q ha hb
    | true =>
      simp only [d927, d75629, d76572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d4451 q = 1) (hb : d75630 q = 1) : d76573 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4451, d75630, d76573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4451, d75630, d76573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h13 (q : Pattern) (ha : d932 q = 1) (hb : d75629 q = 1) : d6181 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d932, d75629, d6181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4487 q ha hb
    | true =>
      simp only [d932, d75629, d6181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d933 q = 1) (hb : d75630 q = 1) : d6182 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d933, d75630, d6182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d933, d75630, d6182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h15 (q : Pattern) (ha : d4452 q = 1) (hb : d75630 q = 1) : d76574 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4452, d76574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4452, d76574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d4453 q = 1) (hb : d75630 q = 1) : d76575 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4453, d76575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4453, d76575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d4454 q = 1) (hb : d75630 q = 1) : d76576 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4454, d76576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4454, d76576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d4455 q = 1) (hb : d75630 q = 1) : d76577 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4455, d76577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4455, d76577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro7453 (p : Pattern) (ha : d4460 p = 1) (hb : d75630 p = 1) : d76582 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d792 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d927 q = 1) (hb : d75629 q = 1) : d76572 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d927, d75629, d76572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7451 q ha hb
    | true =>
      simp only [d927, d75629, d76572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4451 q = 1) (hb : d75630 q = 1) : d76573 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4451, d75630, d76573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4451, d75630, d76573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d932 q = 1) (hb : d75629 q = 1) : d6181 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d932, d75629, d6181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4487 q ha hb
    | true =>
      simp only [d932, d75629, d6181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d933 q = 1) (hb : d75630 q = 1) : d6182 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d933, d75630, d6182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d933, d75630, d6182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d4452 q = 1) (hb : d75630 q = 1) : d76574 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4452, d76574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4452, d76574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4453 q = 1) (hb : d75630 q = 1) : d76575 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4453, d76575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4453, d76575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4454 q = 1) (hb : d75630 q = 1) : d76576 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4454, d76576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4454, d76576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4460 q = 1) (hb : d75630 q = 1) : d76582 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4460, d76582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4460, d76582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7454 (p : Pattern) (ha : d1003 p = 1) (hb : d70145 p = 1) : d6209 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d994 q = 1) : d994 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d999 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1000 q = 1) (hb : d70145 q = 1) : d6206 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1000, d70145, d6206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1000, d70145, d6206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1001 q = 1) (hb : d70145 q = 1) : d6207 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1001, d6207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1001, d6207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1002 q = 1) (hb : d70145 q = 1) : d6208 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1002, d6208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1002, d6208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d1003 q = 1) (hb : d70145 q = 1) : d6209 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1003, d6209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1003, d6209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro7455 (p : Pattern) (ha : d4470 p = 1) (hb : d75630 p = 1) : d76593 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1011 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1012 q = 1) (hb : d75629 q = 1) : d76588 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1012, d75629, d76588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7454 q ha hb
    | true =>
      simp only [d1012, d75629, d76588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4466 q = 1) (hb : d75630 q = 1) : d76589 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4466, d75630, d76589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4466, d75630, d76589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1053 q = 1) (hb : d75629 q = 1) : d6234 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1053, d75629, d6234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4489 q ha hb
    | true =>
      simp only [d1053, d75629, d6234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d1054 q = 1) (hb : d75630 q = 1) : d6235 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1054, d75630, d6235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1054, d75630, d6235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d4467 q = 1) (hb : d75630 q = 1) : d76590 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4467, d76590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4467, d76590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4468 q = 1) (hb : d75630 q = 1) : d76591 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4468, d76591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4468, d76591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4469 q = 1) (hb : d75630 q = 1) : d76592 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4469, d76592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4469, d76592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4470 q = 1) (hb : d75630 q = 1) : d76593 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4470, d76593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4470, d76593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7456 (p : Pattern) (ha : d4476 p = 1) (hb : d75630 p = 1) : d76599 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4456 q = 1) (hb : d75630 q = 1) : d76578 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4456, d76578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7450 q ha hb
    | true =>
      simp only [d4456, d76578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7452 q ha hb
  have h2 (q : Pattern) (ha : d4457 q = 1) (hb : d75630 q = 1) : d76579 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4457, d76579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4457, d76579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4458 q = 1) (hb : d75630 q = 1) : d76580 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4458, d76580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4458, d76580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4459 q = 1) (hb : d75630 q = 1) : d76581 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4459, d76581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4459, d76581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4461 q = 1) (hb : d75630 q = 1) : d76583 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4461, d76583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4461, d76583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7453 q ha hb
  have h6 (q : Pattern) (ha : d4462 q = 1) (hb : d75630 q = 1) : d76584 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4462, d76584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4462, d76584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d4463 q = 1) (hb : d75630 q = 1) : d76585 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4463, d76585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4463, d76585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d4464 q = 1) (hb : d75630 q = 1) : d76586 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4464, d76586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4464, d76586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d4465 q = 1) (hb : d75630 q = 1) : d76587 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4465, d76587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4465, d76587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4471 q = 1) (hb : d75630 q = 1) : d76594 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4471, d76594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4471, d76594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7455 q ha hb
  have h11 (q : Pattern) (ha : d4472 q = 1) (hb : d75630 q = 1) : d76595 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4472, d76595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4472, d76595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4473 q = 1) (hb : d75630 q = 1) : d76596 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4473, d76596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4473, d76596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d4474 q = 1) (hb : d75630 q = 1) : d76597 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4474, d76597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4474, d76597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d4475 q = 1) (hb : d75630 q = 1) : d76598 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4475, d76598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4475, d76598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d4476 q = 1) (hb : d75630 q = 1) : d76599 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d4476, d76599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4476, d76599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro7457 (p : Pattern) (ha : d4482 p = 1) (hb : d75630 p = 1) : d76605 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4477 q = 1) (hb : d75630 q = 1) : d76600 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d4477, d76600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4477, d76600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7456 q ha hb
  have h2 (q : Pattern) (ha : d4478 q = 1) (hb : d75630 q = 1) : d76601 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d4478, d76601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4478, d76601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4479 q = 1) (hb : d75630 q = 1) : d76602 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d4479, d76602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4479, d76602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4480 q = 1) (hb : d75630 q = 1) : d76603 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d4480, d76603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4480, d76603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4481 q = 1) (hb : d75630 q = 1) : d76604 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d4481, d76604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4481, d76604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4482 q = 1) (hb : d75630 q = 1) : d76605 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d4482, d76605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4482, d76605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7458 (p : Pattern) (ha : d1227 p = 1) (hb : d70145 p = 1) : d6291 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1223 q = 1) : d1223 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1150 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1224 q = 1) (hb : d70145 q = 1) : d6288 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1224, d70145, d6288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1224, d70145, d6288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1225 q = 1) (hb : d70145 q = 1) : d6289 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1225, d6289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1225, d6289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1226 q = 1) (hb : d70145 q = 1) : d6290 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1226, d6290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1226, d6290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1227 q = 1) (hb : d70145 q = 1) : d6291 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1227, d6291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1227, d6291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7459 (p : Pattern) (ha : d4489 p = 1) (hb : d75630 p = 1) : d76613 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1158 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1228 q = 1) (hb : d75629 q = 1) : d76608 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1228, d75629, d76608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7458 q ha hb
    | true =>
      simp only [d1228, d75629, d76608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4485 q = 1) (hb : d75630 q = 1) : d76609 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4485, d75630, d76609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4485, d75630, d76609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1320 q = 1) (hb : d75629 q = 1) : d6299 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1320, d75629, d6299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4502 q ha hb
    | true =>
      simp only [d1320, d75629, d6299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d1321 q = 1) (hb : d75630 q = 1) : d6300 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1321, d75630, d6300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1321, d75630, d6300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d4486 q = 1) (hb : d75630 q = 1) : d76610 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4486, d76610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4486, d76610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4487 q = 1) (hb : d75630 q = 1) : d76611 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4487, d76611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4487, d76611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4488 q = 1) (hb : d75630 q = 1) : d76612 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4488, d76612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4488, d76612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4489 q = 1) (hb : d75630 q = 1) : d76613 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4489, d76613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4489, d76613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7460 (p : Pattern) (ha : d1337 p = 1) (hb : d70145 p = 1) : d6314 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1223 q = 1) : d1223 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1150 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1224 q = 1) (hb : d70145 q = 1) : d6288 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1224, d70145, d6288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1224, d70145, d6288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1225 q = 1) (hb : d70145 q = 1) : d6289 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1225, d6289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1225, d6289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1226 q = 1) (hb : d70145 q = 1) : d6290 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1226, d6290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1226, d6290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d1337 q = 1) (hb : d70145 q = 1) : d6314 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1337, d6314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1337, d6314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro7461 (p : Pattern) (ha : d4494 p = 1) (hb : d75630 p = 1) : d76619 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1158 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1228 q = 1) (hb : d75629 q = 1) : d76608 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1228, d75629, d76608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7458 q ha hb
    | true =>
      simp only [d1228, d75629, d76608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4485 q = 1) (hb : d75630 q = 1) : d76609 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4485, d75630, d76609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4485, d75630, d76609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1320 q = 1) (hb : d75629 q = 1) : d6299 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1320, d75629, d6299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4502 q ha hb
    | true =>
      simp only [d1320, d75629, d6299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d1321 q = 1) (hb : d75630 q = 1) : d6300 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1321, d75630, d6300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1321, d75630, d6300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d4486 q = 1) (hb : d75630 q = 1) : d76610 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4486, d76610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4486, d76610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4487 q = 1) (hb : d75630 q = 1) : d76611 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4487, d76611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4487, d76611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4488 q = 1) (hb : d75630 q = 1) : d76612 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4488, d76612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4488, d76612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d1171 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d1338 q = 1) (hb : d75629 q = 1) : d76614 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1338, d75629, d76614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7460 q ha hb
    | true =>
      simp only [d1338, d75629, d76614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d4490 q = 1) (hb : d75630 q = 1) : d76615 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4490, d75630, d76615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4490, d75630, d76615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h13 (q : Pattern) (ha : d1343 q = 1) (hb : d75629 q = 1) : d6320 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1343, d75629, d6320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4498 q ha hb
    | true =>
      simp only [d1343, d75629, d6320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d1344 q = 1) (hb : d75630 q = 1) : d6321 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1344, d75630, d6321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1344, d75630, d6321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h15 (q : Pattern) (ha : d4491 q = 1) (hb : d75630 q = 1) : d76616 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4491, d76616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4491, d76616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d4492 q = 1) (hb : d75630 q = 1) : d76617 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4492, d76617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4492, d76617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d4493 q = 1) (hb : d75630 q = 1) : d76618 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4493, d76618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4493, d76618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d4494 q = 1) (hb : d75630 q = 1) : d76619 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4494, d76619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4494, d76619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro7462 (p : Pattern) (ha : d4499 p = 1) (hb : d75630 p = 1) : d76624 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1171 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1338 q = 1) (hb : d75629 q = 1) : d76614 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1338, d75629, d76614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7460 q ha hb
    | true =>
      simp only [d1338, d75629, d76614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4490 q = 1) (hb : d75630 q = 1) : d76615 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4490, d75630, d76615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4490, d75630, d76615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1343 q = 1) (hb : d75629 q = 1) : d6320 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1343, d75629, d6320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4498 q ha hb
    | true =>
      simp only [d1343, d75629, d6320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d1344 q = 1) (hb : d75630 q = 1) : d6321 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1344, d75630, d6321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1344, d75630, d6321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d4491 q = 1) (hb : d75630 q = 1) : d76616 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4491, d76616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4491, d76616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4492 q = 1) (hb : d75630 q = 1) : d76617 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4492, d76617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4492, d76617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4493 q = 1) (hb : d75630 q = 1) : d76618 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4493, d76618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4493, d76618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4499 q = 1) (hb : d75630 q = 1) : d76624 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4499, d76624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4499, d76624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7463 (p : Pattern) (ha : d1428 p = 1) (hb : d70145 p = 1) : d6348 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1419 q = 1) : d1419 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1424 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1425 q = 1) (hb : d70145 q = 1) : d6345 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1425, d70145, d6345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1425, d70145, d6345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1426 q = 1) (hb : d70145 q = 1) : d6346 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1426, d6346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1426, d6346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1427 q = 1) (hb : d70145 q = 1) : d6347 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1427, d6347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1427, d6347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d1428 q = 1) (hb : d70145 q = 1) : d6348 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1428, d6348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1428, d6348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro7464 (p : Pattern) (ha : d4509 p = 1) (hb : d75630 p = 1) : d76635 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1436 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1437 q = 1) (hb : d75629 q = 1) : d76630 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1437, d75629, d76630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7463 q ha hb
    | true =>
      simp only [d1437, d75629, d76630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4505 q = 1) (hb : d75630 q = 1) : d76631 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4505, d75630, d76631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4505, d75630, d76631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1487 q = 1) (hb : d75629 q = 1) : d6379 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1487, d75629, d6379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4500 q ha hb
    | true =>
      simp only [d1487, d75629, d6379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d1488 q = 1) (hb : d75630 q = 1) : d6380 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1488, d75630, d6380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1488, d75630, d6380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d4506 q = 1) (hb : d75630 q = 1) : d76632 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4506, d76632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4506, d76632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4507 q = 1) (hb : d75630 q = 1) : d76633 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4507, d76633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4507, d76633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4508 q = 1) (hb : d75630 q = 1) : d76634 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4508, d76634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4508, d76634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4509 q = 1) (hb : d75630 q = 1) : d76635 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4509, d76635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4509, d76635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7465 (p : Pattern) (ha : d4515 p = 1) (hb : d75630 p = 1) : d76641 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4495 q = 1) (hb : d75630 q = 1) : d76620 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4495, d76620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7459 q ha hb
    | true =>
      simp only [d4495, d76620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7461 q ha hb
  have h2 (q : Pattern) (ha : d4496 q = 1) (hb : d75630 q = 1) : d76621 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4496, d76621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4496, d76621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4497 q = 1) (hb : d75630 q = 1) : d76622 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4497, d76622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4497, d76622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4498 q = 1) (hb : d75630 q = 1) : d76623 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4498, d76623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4498, d76623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4500 q = 1) (hb : d75630 q = 1) : d76625 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4500, d76625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4500, d76625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7462 q ha hb
  have h6 (q : Pattern) (ha : d4501 q = 1) (hb : d75630 q = 1) : d76626 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4501, d76626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4501, d76626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d4502 q = 1) (hb : d75630 q = 1) : d76627 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4502, d76627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4502, d76627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d4503 q = 1) (hb : d75630 q = 1) : d76628 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4503, d76628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4503, d76628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d4504 q = 1) (hb : d75630 q = 1) : d76629 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4504, d76629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4504, d76629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4510 q = 1) (hb : d75630 q = 1) : d76636 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4510, d76636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4510, d76636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7464 q ha hb
  have h11 (q : Pattern) (ha : d4511 q = 1) (hb : d75630 q = 1) : d76637 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4511, d76637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4511, d76637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4512 q = 1) (hb : d75630 q = 1) : d76638 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4512, d76638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4512, d76638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d4513 q = 1) (hb : d75630 q = 1) : d76639 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4513, d76639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4513, d76639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d4514 q = 1) (hb : d75630 q = 1) : d76640 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4514, d76640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4514, d76640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d4515 q = 1) (hb : d75630 q = 1) : d76641 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d4515, d76641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4515, d76641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro7466 (p : Pattern) (ha : d4521 p = 1) (hb : d75630 p = 1) : d76647 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4516 q = 1) (hb : d75630 q = 1) : d76642 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d4516, d76642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4516, d76642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7465 q ha hb
  have h2 (q : Pattern) (ha : d4517 q = 1) (hb : d75630 q = 1) : d76643 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d4517, d76643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4517, d76643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4518 q = 1) (hb : d75630 q = 1) : d76644 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d4518, d76644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4518, d76644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4519 q = 1) (hb : d75630 q = 1) : d76645 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d4519, d76645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4519, d76645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4520 q = 1) (hb : d75630 q = 1) : d76646 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d4520, d76646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4520, d76646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4521 q = 1) (hb : d75630 q = 1) : d76647 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d4521, d76647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4521, d76647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7467 (p : Pattern) (ha : d1682 p = 1) (hb : d70145 p = 1) : d6437 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1678 q = 1) : d1678 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1611 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1679 q = 1) (hb : d70145 q = 1) : d6434 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1679, d70145, d6434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1679, d70145, d6434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1680 q = 1) (hb : d70145 q = 1) : d6435 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1680, d6435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1680, d6435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1681 q = 1) (hb : d70145 q = 1) : d6436 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1681, d6436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1681, d6436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1682 q = 1) (hb : d70145 q = 1) : d6437 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1682, d6437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1682, d6437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7468 (p : Pattern) (ha : d4529 p = 1) (hb : d75630 p = 1) : d76656 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1619 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1683 q = 1) (hb : d75629 q = 1) : d76651 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1683, d75629, d76651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7467 q ha hb
    | true =>
      simp only [d1683, d75629, d76651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4525 q = 1) (hb : d75630 q = 1) : d76652 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4525, d75630, d76652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4525, d75630, d76652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1797 q = 1) (hb : d75629 q = 1) : d6445 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1797, d75629, d6445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4513 q ha hb
    | true =>
      simp only [d1797, d75629, d6445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d1798 q = 1) (hb : d75630 q = 1) : d6446 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1798, d75630, d6446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1798, d75630, d6446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d4526 q = 1) (hb : d75630 q = 1) : d76653 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4526, d76653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4526, d76653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4527 q = 1) (hb : d75630 q = 1) : d76654 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4527, d76654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4527, d76654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4528 q = 1) (hb : d75630 q = 1) : d76655 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4528, d76655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4528, d76655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4529 q = 1) (hb : d75630 q = 1) : d76656 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4529, d76656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4529, d76656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7469 (p : Pattern) (ha : d1814 p = 1) (hb : d70145 p = 1) : d6460 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1678 q = 1) : d1678 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1611 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1679 q = 1) (hb : d70145 q = 1) : d6434 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1679, d70145, d6434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1679, d70145, d6434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1680 q = 1) (hb : d70145 q = 1) : d6435 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1680, d6435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1680, d6435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1681 q = 1) (hb : d70145 q = 1) : d6436 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1681, d6436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1681, d6436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d1814 q = 1) (hb : d70145 q = 1) : d6460 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1814, d6460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1814, d6460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro7470 (p : Pattern) (ha : d4534 p = 1) (hb : d75630 p = 1) : d76662 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1619 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1683 q = 1) (hb : d75629 q = 1) : d76651 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1683, d75629, d76651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7467 q ha hb
    | true =>
      simp only [d1683, d75629, d76651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4525 q = 1) (hb : d75630 q = 1) : d76652 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4525, d75630, d76652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4525, d75630, d76652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1797 q = 1) (hb : d75629 q = 1) : d6445 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1797, d75629, d6445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4513 q ha hb
    | true =>
      simp only [d1797, d75629, d6445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d1798 q = 1) (hb : d75630 q = 1) : d6446 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1798, d75630, d6446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1798, d75630, d6446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d4526 q = 1) (hb : d75630 q = 1) : d76653 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4526, d76653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4526, d76653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4527 q = 1) (hb : d75630 q = 1) : d76654 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4527, d76654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4527, d76654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4528 q = 1) (hb : d75630 q = 1) : d76655 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4528, d76655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4528, d76655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d1632 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d1815 q = 1) (hb : d75629 q = 1) : d76657 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1815, d75629, d76657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7469 q ha hb
    | true =>
      simp only [d1815, d75629, d76657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d4530 q = 1) (hb : d75630 q = 1) : d76658 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4530, d75630, d76658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4530, d75630, d76658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h13 (q : Pattern) (ha : d1820 q = 1) (hb : d75629 q = 1) : d6466 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1820, d75629, d6466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4509 q ha hb
    | true =>
      simp only [d1820, d75629, d6466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d1821 q = 1) (hb : d75630 q = 1) : d6467 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1821, d75630, d6467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1821, d75630, d6467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h15 (q : Pattern) (ha : d4531 q = 1) (hb : d75630 q = 1) : d76659 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4531, d76659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4531, d76659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d4532 q = 1) (hb : d75630 q = 1) : d76660 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4532, d76660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4532, d76660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d4533 q = 1) (hb : d75630 q = 1) : d76661 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4533, d76661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4533, d76661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d4534 q = 1) (hb : d75630 q = 1) : d76662 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4534, d76662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4534, d76662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro7471 (p : Pattern) (ha : d4539 p = 1) (hb : d75630 p = 1) : d76667 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1632 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1815 q = 1) (hb : d75629 q = 1) : d76657 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1815, d75629, d76657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7469 q ha hb
    | true =>
      simp only [d1815, d75629, d76657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4530 q = 1) (hb : d75630 q = 1) : d76658 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4530, d75630, d76658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4530, d75630, d76658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1820 q = 1) (hb : d75629 q = 1) : d6466 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1820, d75629, d6466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4509 q ha hb
    | true =>
      simp only [d1820, d75629, d6466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d1821 q = 1) (hb : d75630 q = 1) : d6467 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1821, d75630, d6467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1821, d75630, d6467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d4531 q = 1) (hb : d75630 q = 1) : d76659 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4531, d76659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4531, d76659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4532 q = 1) (hb : d75630 q = 1) : d76660 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4532, d76660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4532, d76660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4533 q = 1) (hb : d75630 q = 1) : d76661 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4533, d76661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4533, d76661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4539 q = 1) (hb : d75630 q = 1) : d76667 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4539, d76667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4539, d76667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7472 (p : Pattern) (ha : d1905 p = 1) (hb : d70145 p = 1) : d6494 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1896 q = 1) : d1896 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1901 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1902 q = 1) (hb : d70145 q = 1) : d6491 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1902, d70145, d6491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1902, d70145, d6491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1903 q = 1) (hb : d70145 q = 1) : d6492 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1903, d6492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1903, d6492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1904 q = 1) (hb : d70145 q = 1) : d6493 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1904, d6493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1904, d6493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d1905 q = 1) (hb : d70145 q = 1) : d6494 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1905, d6494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1905, d6494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro7473 (p : Pattern) (ha : d4549 p = 1) (hb : d75630 p = 1) : d76678 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1913 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1914 q = 1) (hb : d75629 q = 1) : d76673 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1914, d75629, d76673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7472 q ha hb
    | true =>
      simp only [d1914, d75629, d76673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4545 q = 1) (hb : d75630 q = 1) : d76674 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4545, d75630, d76674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4545, d75630, d76674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1964 q = 1) (hb : d75629 q = 1) : d6525 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1964, d75629, d6525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4511 q ha hb
    | true =>
      simp only [d1964, d75629, d6525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d1965 q = 1) (hb : d75630 q = 1) : d6526 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1965, d75630, d6526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1965, d75630, d6526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d4546 q = 1) (hb : d75630 q = 1) : d76675 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4546, d76675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4546, d76675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4547 q = 1) (hb : d75630 q = 1) : d76676 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4547, d76676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4547, d76676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4548 q = 1) (hb : d75630 q = 1) : d76677 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4548, d76677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4548, d76677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4549 q = 1) (hb : d75630 q = 1) : d76678 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4549, d76678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4549, d76678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7474 (p : Pattern) (ha : d4555 p = 1) (hb : d75630 p = 1) : d76684 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4535 q = 1) (hb : d75630 q = 1) : d76663 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4535, d76663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7468 q ha hb
    | true =>
      simp only [d4535, d76663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7470 q ha hb
  have h2 (q : Pattern) (ha : d4536 q = 1) (hb : d75630 q = 1) : d76664 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4536, d76664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4536, d76664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4537 q = 1) (hb : d75630 q = 1) : d76665 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4537, d76665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4537, d76665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4538 q = 1) (hb : d75630 q = 1) : d76666 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4538, d76666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4538, d76666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4540 q = 1) (hb : d75630 q = 1) : d76668 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4540, d76668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4540, d76668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7471 q ha hb
  have h6 (q : Pattern) (ha : d4541 q = 1) (hb : d75630 q = 1) : d76669 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4541, d76669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4541, d76669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d4542 q = 1) (hb : d75630 q = 1) : d76670 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4542, d76670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4542, d76670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d4543 q = 1) (hb : d75630 q = 1) : d76671 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4543, d76671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4543, d76671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d4544 q = 1) (hb : d75630 q = 1) : d76672 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4544, d76672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4544, d76672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4550 q = 1) (hb : d75630 q = 1) : d76679 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4550, d76679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4550, d76679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7473 q ha hb
  have h11 (q : Pattern) (ha : d4551 q = 1) (hb : d75630 q = 1) : d76680 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4551, d76680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4551, d76680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4552 q = 1) (hb : d75630 q = 1) : d76681 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4552, d76681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4552, d76681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d4553 q = 1) (hb : d75630 q = 1) : d76682 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4553, d76682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4553, d76682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d4554 q = 1) (hb : d75630 q = 1) : d76683 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4554, d76683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4554, d76683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d4555 q = 1) (hb : d75630 q = 1) : d76684 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d4555, d76684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4555, d76684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro7475 (p : Pattern) (ha : d4561 p = 1) (hb : d75630 p = 1) : d76690 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4556 q = 1) (hb : d75630 q = 1) : d76685 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d4556, d76685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4556, d76685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7474 q ha hb
  have h2 (q : Pattern) (ha : d4557 q = 1) (hb : d75630 q = 1) : d76686 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d4557, d76686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4557, d76686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4558 q = 1) (hb : d75630 q = 1) : d76687 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d4558, d76687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4558, d76687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4559 q = 1) (hb : d75630 q = 1) : d76688 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d4559, d76688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4559, d76688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4560 q = 1) (hb : d75630 q = 1) : d76689 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d4560, d76689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4560, d76689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4561 q = 1) (hb : d75630 q = 1) : d76690 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d4561, d76690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4561, d76690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7476 (p : Pattern) (ha : d2161 p = 1) (hb : d70145 p = 1) : d6584 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d2157 q = 1) : d2157 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2094 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2158 q = 1) (hb : d70145 q = 1) : d6581 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2158, d70145, d6581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2158, d70145, d6581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2159 q = 1) (hb : d70145 q = 1) : d6582 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2159, d6582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2159, d6582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2160 q = 1) (hb : d70145 q = 1) : d6583 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2160, d6583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2160, d6583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2161 q = 1) (hb : d70145 q = 1) : d6584 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2161, d6584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2161, d6584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7477 (p : Pattern) (ha : d4570 p = 1) (hb : d75630 p = 1) : d76700 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2102 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2162 q = 1) (hb : d75629 q = 1) : d76695 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2162, d75629, d76695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7476 q ha hb
    | true =>
      simp only [d2162, d75629, d76695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4566 q = 1) (hb : d75630 q = 1) : d76696 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4566, d75630, d76696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4566, d75630, d76696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2275 q = 1) (hb : d75629 q = 1) : d6592 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2275, d75629, d6592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4524 q ha hb
    | true =>
      simp only [d2275, d75629, d6592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d2276 q = 1) (hb : d75630 q = 1) : d6593 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2276, d75630, d6593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2276, d75630, d6593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d4567 q = 1) (hb : d75630 q = 1) : d76697 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4567, d76697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4567, d76697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4568 q = 1) (hb : d75630 q = 1) : d76698 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4568, d76698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4568, d76698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4569 q = 1) (hb : d75630 q = 1) : d76699 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4569, d76699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4569, d76699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4570 q = 1) (hb : d75630 q = 1) : d76700 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4570, d76700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4570, d76700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7478 (p : Pattern) (ha : d2292 p = 1) (hb : d70145 p = 1) : d6607 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2157 q = 1) : d2157 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2094 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2158 q = 1) (hb : d70145 q = 1) : d6581 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2158, d70145, d6581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2158, d70145, d6581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2159 q = 1) (hb : d70145 q = 1) : d6582 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2159, d6582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2159, d6582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2160 q = 1) (hb : d70145 q = 1) : d6583 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2160, d6583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2160, d6583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d2292 q = 1) (hb : d70145 q = 1) : d6607 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2292, d6607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2292, d6607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro7479 (p : Pattern) (ha : d4575 p = 1) (hb : d75630 p = 1) : d76706 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2102 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2162 q = 1) (hb : d75629 q = 1) : d76695 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2162, d75629, d76695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7476 q ha hb
    | true =>
      simp only [d2162, d75629, d76695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4566 q = 1) (hb : d75630 q = 1) : d76696 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4566, d75630, d76696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4566, d75630, d76696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2275 q = 1) (hb : d75629 q = 1) : d6592 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2275, d75629, d6592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4524 q ha hb
    | true =>
      simp only [d2275, d75629, d6592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d2276 q = 1) (hb : d75630 q = 1) : d6593 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2276, d75630, d6593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2276, d75630, d6593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d4567 q = 1) (hb : d75630 q = 1) : d76697 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4567, d76697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4567, d76697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4568 q = 1) (hb : d75630 q = 1) : d76698 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4568, d76698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4568, d76698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4569 q = 1) (hb : d75630 q = 1) : d76699 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4569, d76699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4569, d76699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d2115 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d2293 q = 1) (hb : d75629 q = 1) : d76701 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2293, d75629, d76701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7478 q ha hb
    | true =>
      simp only [d2293, d75629, d76701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d4571 q = 1) (hb : d75630 q = 1) : d76702 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4571, d75630, d76702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4571, d75630, d76702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h13 (q : Pattern) (ha : d2298 q = 1) (hb : d75629 q = 1) : d6613 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2298, d75629, d6613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4520 q ha hb
    | true =>
      simp only [d2298, d75629, d6613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d2299 q = 1) (hb : d75630 q = 1) : d6614 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2299, d75630, d6614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d2299, d75630, d6614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h15 (q : Pattern) (ha : d4572 q = 1) (hb : d75630 q = 1) : d76703 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4572, d76703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4572, d76703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d4573 q = 1) (hb : d75630 q = 1) : d76704 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4573, d76704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4573, d76704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d4574 q = 1) (hb : d75630 q = 1) : d76705 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4574, d76705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4574, d76705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d4575 q = 1) (hb : d75630 q = 1) : d76706 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4575, d76706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4575, d76706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro7480 (p : Pattern) (ha : d4580 p = 1) (hb : d75630 p = 1) : d76711 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2115 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2293 q = 1) (hb : d75629 q = 1) : d76701 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2293, d75629, d76701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7478 q ha hb
    | true =>
      simp only [d2293, d75629, d76701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4571 q = 1) (hb : d75630 q = 1) : d76702 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4571, d75630, d76702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4571, d75630, d76702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2298 q = 1) (hb : d75629 q = 1) : d6613 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2298, d75629, d6613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4520 q ha hb
    | true =>
      simp only [d2298, d75629, d6613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d2299 q = 1) (hb : d75630 q = 1) : d6614 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2299, d75630, d6614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2299, d75630, d6614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d4572 q = 1) (hb : d75630 q = 1) : d76703 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4572, d76703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4572, d76703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4573 q = 1) (hb : d75630 q = 1) : d76704 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4573, d76704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4573, d76704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4574 q = 1) (hb : d75630 q = 1) : d76705 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4574, d76705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4574, d76705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4580 q = 1) (hb : d75630 q = 1) : d76711 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4580, d76711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4580, d76711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7481 (p : Pattern) (ha : d2383 p = 1) (hb : d70145 p = 1) : d6641 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2374 q = 1) : d2374 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2379 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2380 q = 1) (hb : d70145 q = 1) : d6638 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2380, d70145, d6638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2380, d70145, d6638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2381 q = 1) (hb : d70145 q = 1) : d6639 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2381, d6639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2381, d6639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2382 q = 1) (hb : d70145 q = 1) : d6640 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2382, d6640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2382, d6640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d2383 q = 1) (hb : d70145 q = 1) : d6641 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2383, d6641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2383, d6641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro7482 (p : Pattern) (ha : d4590 p = 1) (hb : d75630 p = 1) : d76722 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2391 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2392 q = 1) (hb : d75629 q = 1) : d76717 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2392, d75629, d76717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7481 q ha hb
    | true =>
      simp only [d2392, d75629, d76717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4586 q = 1) (hb : d75630 q = 1) : d76718 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4586, d75630, d76718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4586, d75630, d76718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2442 q = 1) (hb : d75629 q = 1) : d6672 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2442, d75629, d6672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4522 q ha hb
    | true =>
      simp only [d2442, d75629, d6672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d2443 q = 1) (hb : d75630 q = 1) : d6673 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2443, d75630, d6673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2443, d75630, d6673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d4587 q = 1) (hb : d75630 q = 1) : d76719 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4587, d76719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4587, d76719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4588 q = 1) (hb : d75630 q = 1) : d76720 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4588, d76720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4588, d76720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4589 q = 1) (hb : d75630 q = 1) : d76721 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4589, d76721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4589, d76721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4590 q = 1) (hb : d75630 q = 1) : d76722 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4590, d76722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4590, d76722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7483 (p : Pattern) (ha : d4596 p = 1) (hb : d75630 p = 1) : d76728 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4576 q = 1) (hb : d75630 q = 1) : d76707 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4576, d76707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7477 q ha hb
    | true =>
      simp only [d4576, d76707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7479 q ha hb
  have h2 (q : Pattern) (ha : d4577 q = 1) (hb : d75630 q = 1) : d76708 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4577, d76708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4577, d76708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4578 q = 1) (hb : d75630 q = 1) : d76709 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4578, d76709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4578, d76709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4579 q = 1) (hb : d75630 q = 1) : d76710 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4579, d76710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4579, d76710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4581 q = 1) (hb : d75630 q = 1) : d76712 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4581, d76712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4581, d76712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7480 q ha hb
  have h6 (q : Pattern) (ha : d4582 q = 1) (hb : d75630 q = 1) : d76713 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4582, d76713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4582, d76713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d4583 q = 1) (hb : d75630 q = 1) : d76714 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4583, d76714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4583, d76714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d4584 q = 1) (hb : d75630 q = 1) : d76715 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4584, d76715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4584, d76715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d4585 q = 1) (hb : d75630 q = 1) : d76716 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4585, d76716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4585, d76716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4591 q = 1) (hb : d75630 q = 1) : d76723 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4591, d76723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4591, d76723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7482 q ha hb
  have h11 (q : Pattern) (ha : d4592 q = 1) (hb : d75630 q = 1) : d76724 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4592, d76724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4592, d76724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4593 q = 1) (hb : d75630 q = 1) : d76725 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4593, d76725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4593, d76725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d4594 q = 1) (hb : d75630 q = 1) : d76726 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4594, d76726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4594, d76726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d4595 q = 1) (hb : d75630 q = 1) : d76727 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4595, d76727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4595, d76727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d4596 q = 1) (hb : d75630 q = 1) : d76728 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d4596, d76728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4596, d76728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro7484 (p : Pattern) (ha : d4602 p = 1) (hb : d75630 p = 1) : d76734 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4597 q = 1) (hb : d75630 q = 1) : d76729 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d4597, d76729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4597, d76729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7483 q ha hb
  have h2 (q : Pattern) (ha : d4598 q = 1) (hb : d75630 q = 1) : d76730 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d4598, d76730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4598, d76730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4599 q = 1) (hb : d75630 q = 1) : d76731 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d4599, d76731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4599, d76731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4600 q = 1) (hb : d75630 q = 1) : d76732 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d4600, d76732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4600, d76732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4601 q = 1) (hb : d75630 q = 1) : d76733 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d4601, d76733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4601, d76733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4602 q = 1) (hb : d75630 q = 1) : d76734 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d4602, d76734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4602, d76734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7485 (p : Pattern) (ha : d4608 p = 1) (hb : d75630 p = 1) : d76740 p = 1 := by
  have h0 (q : Pattern) (ha : d4445 q = 1) (hb : d75630 q = 1) : d76565 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d4445, d76565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7439 q ha hb
    | true =>
      simp only [d4445, d76565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7448 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4483 q = 1) (hb : d75630 q = 1) : d76606 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d4483, d76606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4483, d76606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7457 q ha hb
  have h3 (q : Pattern) (ha : d4484 q = 1) (hb : d75630 q = 1) : d76607 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d4484, d76607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4484, d76607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4522 q = 1) (hb : d75630 q = 1) : d76648 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d4522, d76648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4522, d76648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7466 q ha hb
  have h5 (q : Pattern) (ha : d4523 q = 1) (hb : d75630 q = 1) : d76649 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d4523, d76649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4523, d76649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4524 q = 1) (hb : d75630 q = 1) : d76650 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d4524, d76650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4524, d76650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4562 q = 1) (hb : d75630 q = 1) : d76691 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d4562, d76691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4562, d76691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7475 q ha hb
  have h8 (q : Pattern) (ha : d4563 q = 1) (hb : d75630 q = 1) : d76692 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d4563, d76692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4563, d76692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4564 q = 1) (hb : d75630 q = 1) : d76693 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d4564, d76693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4564, d76693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4565 q = 1) (hb : d75630 q = 1) : d76694 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d4565, d76694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4565, d76694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4603 q = 1) (hb : d75630 q = 1) : d76735 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d4603, d76735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4603, d76735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7484 q ha hb
  have h12 (q : Pattern) (ha : d4604 q = 1) (hb : d75630 q = 1) : d76736 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d4604, d76736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4604, d76736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d4605 q = 1) (hb : d75630 q = 1) : d76737 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d4605, d76737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4605, d76737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d4606 q = 1) (hb : d75630 q = 1) : d76738 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d4606, d76738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4606, d76738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d4607 q = 1) (hb : d75630 q = 1) : d76739 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d4607, d76739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4607, d76739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d4608 q = 1) (hb : d75630 q = 1) : d76740 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d4608, d76740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d4608, d76740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro7486 (p : Pattern) (ha : d4614 p = 1) (hb : d75630 p = 1) : d76746 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4609 q = 1) (hb : d75630 q = 1) : d76741 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d4609, d76741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7485 q ha hb
    | true =>
      simp only [d4609, d76741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4610 q = 1) (hb : d75630 q = 1) : d76742 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d4610, d76742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4610, d76742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4611 q = 1) (hb : d75630 q = 1) : d76743 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d4611, d76743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4611, d76743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4612 q = 1) (hb : d75630 q = 1) : d76744 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d4612, d76744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4612, d76744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4613 q = 1) (hb : d75630 q = 1) : d76745 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d4613, d76745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4613, d76745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4614 q = 1) (hb : d75630 q = 1) : d76746 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d4614, d76746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4614, d76746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7487 (p : Pattern) (ha : d4620 p = 1) (hb : d75630 p = 1) : d76752 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4615 q = 1) (hb : d75630 q = 1) : d76747 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d4615, d76747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7486 q ha hb
    | true =>
      simp only [d4615, d76747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4616 q = 1) (hb : d75630 q = 1) : d76748 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d4616, d76748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4616, d76748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4617 q = 1) (hb : d75630 q = 1) : d76749 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d4617, d76749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4617, d76749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4618 q = 1) (hb : d75630 q = 1) : d76750 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d4618, d76750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4618, d76750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4619 q = 1) (hb : d75630 q = 1) : d76751 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d4619, d76751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4619, d76751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4620 q = 1) (hb : d75630 q = 1) : d76752 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d4620, d76752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4620, d76752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7488 (p : Pattern) (ha : d4626 p = 1) (hb : d75630 p = 1) : d76758 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4621 q = 1) (hb : d75630 q = 1) : d76753 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d4621, d76753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7487 q ha hb
    | true =>
      simp only [d4621, d76753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4622 q = 1) (hb : d75630 q = 1) : d76754 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d4622, d76754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4622, d76754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4623 q = 1) (hb : d75630 q = 1) : d76755 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d4623, d76755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4623, d76755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4624 q = 1) (hb : d75630 q = 1) : d76756 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d4624, d76756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4624, d76756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4625 q = 1) (hb : d75630 q = 1) : d76757 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d4625, d76757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4625, d76757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4626 q = 1) (hb : d75630 q = 1) : d76758 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d4626, d76758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4626, d76758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7489 (p : Pattern) (ha : d4632 p = 1) (hb : d75630 p = 1) : d76764 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4627 q = 1) (hb : d75630 q = 1) : d76759 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d4627, d76759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7488 q ha hb
    | true =>
      simp only [d4627, d76759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4628 q = 1) (hb : d75630 q = 1) : d76760 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d4628, d76760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4628, d76760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4629 q = 1) (hb : d75630 q = 1) : d76761 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d4629, d76761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4629, d76761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4630 q = 1) (hb : d75630 q = 1) : d76762 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d4630, d76762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4630, d76762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4631 q = 1) (hb : d75630 q = 1) : d76763 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d4631, d76763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4631, d76763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4632 q = 1) (hb : d75630 q = 1) : d76764 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d4632, d76764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4632, d76764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7490 (p : Pattern) (ha : d4638 p = 1) (hb : d75630 p = 1) : d76770 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4633 q = 1) (hb : d75630 q = 1) : d76765 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d4633, d76765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7489 q ha hb
    | true =>
      simp only [d4633, d76765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4634 q = 1) (hb : d75630 q = 1) : d76766 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d4634, d76766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4634, d76766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4635 q = 1) (hb : d75630 q = 1) : d76767 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d4635, d76767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4635, d76767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4636 q = 1) (hb : d75630 q = 1) : d76768 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d4636, d76768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4636, d76768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4637 q = 1) (hb : d75630 q = 1) : d76769 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d4637, d76769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4637, d76769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4638 q = 1) (hb : d75630 q = 1) : d76770 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d4638, d76770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4638, d76770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7491 (p : Pattern) (ha : d4644 p = 1) (hb : d75630 p = 1) : d76776 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4639 q = 1) (hb : d75630 q = 1) : d76771 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d4639, d76771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7490 q ha hb
    | true =>
      simp only [d4639, d76771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4640 q = 1) (hb : d75630 q = 1) : d76772 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d4640, d76772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4640, d76772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4641 q = 1) (hb : d75630 q = 1) : d76773 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d4641, d76773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4641, d76773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4642 q = 1) (hb : d75630 q = 1) : d76774 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d4642, d76774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4642, d76774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4643 q = 1) (hb : d75630 q = 1) : d76775 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d4643, d76775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4643, d76775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4644 q = 1) (hb : d75630 q = 1) : d76776 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d4644, d76776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4644, d76776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7492 (p : Pattern) (ha : d4650 p = 1) (hb : d75630 p = 1) : d76782 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4645 q = 1) (hb : d75630 q = 1) : d76777 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d4645, d76777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7491 q ha hb
    | true =>
      simp only [d4645, d76777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4646 q = 1) (hb : d75630 q = 1) : d76778 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d4646, d76778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4646, d76778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4647 q = 1) (hb : d75630 q = 1) : d76779 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d4647, d76779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4647, d76779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4648 q = 1) (hb : d75630 q = 1) : d76780 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d4648, d76780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4648, d76780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4649 q = 1) (hb : d75630 q = 1) : d76781 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d4649, d76781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4649, d76781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4650 q = 1) (hb : d75630 q = 1) : d76782 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d4650, d76782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4650, d76782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7493 (p : Pattern) (ha : d4736 p = 1) (hb : d68835 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21 q ha hb
    | true =>
      simp only [d151, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4733 q = 1) (hb : d68832 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d68832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4733, d68832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4734 q = 1) (hb : d68833 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4734, d68833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4734, d68833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4735 q = 1) (hb : d68834 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4735, d68834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4735, d68834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4736 q = 1) (hb : d68835 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d4736, d68835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4736, d68835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7494 (p : Pattern) (ha : d75636 p = 1) (hb : d76455 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d51894 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4737 q = 1) (hb : d75631 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d75631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7493 q ha hb
    | true =>
      simp only [d4737, d75631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d5350 q = 1) (hb : d75632 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, d75632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5350, d75632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d75633 q = 1) (hb : d76452 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75633, d76452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d75633, d76452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d75634 q = 1) (hb : d76453 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75634, d76453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d75634, d76453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d75635 q = 1) (hb : d76454 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75635, d76454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d75635, d76454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d75636 q = 1) (hb : d76455 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75636, d76455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75636, d76455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro7495 (p : Pattern) (ha : d5355 p = 1) (hb : d74081 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21 q ha hb
    | true =>
      simp only [d151, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4733 q = 1) (hb : d68832 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d68832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4733, d68832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4734 q = 1) (hb : d68833 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4734, d68833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4734, d68833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4735 q = 1) (hb : d68834 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4735, d68834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4735, d68834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5355 q = 1) (hb : d74081 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5355, d74081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5355, d74081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7496 (p : Pattern) (ha : d75642 p = 1) (hb : d76459 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51894 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4737 q = 1) (hb : d75631 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d75631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7493 q ha hb
    | true =>
      simp only [d4737, d75631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5350 q = 1) (hb : d75632 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, d75632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5350, d75632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d75633 q = 1) (hb : d76452 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75633, d76452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d75633, d76452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d75634 q = 1) (hb : d76453 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75634, d76453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d75634, d76453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d75635 q = 1) (hb : d76454 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75635, d76454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75635, d76454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d52018 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d52022 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d51901 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d5356 q = 1) (hb : d75637 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d75637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7495 q ha hb
    | true =>
      simp only [d5356, d75637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d5357 q = 1) (hb : d75638 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, d75638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d5357, d75638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d50 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h19 (q : Pattern) (ha : d51 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h20 (q : Pattern) (ha : d75639 q = 1) (hb : d76456 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75639, d76456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
    | true =>
      simp only [d75639, d76456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d75640 q = 1) (hb : d76457 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75640, d76457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d75640, d76457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d75641 q = 1) (hb : d76458 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75641, d76458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d75641, d76458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d75642 q = 1) (hb : d76459 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75642, d76459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d75642, d76459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro7497 (p : Pattern) (ha : d75649 p = 1) (hb : d76464 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51901 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5356 q = 1) (hb : d75637 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d75637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7495 q ha hb
    | true =>
      simp only [d5356, d75637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5357 q = 1) (hb : d75638 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, d75638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5357, d75638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d50 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d51 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d75639 q = 1) (hb : d76456 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75639, d76456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d75639, d76456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d75647 q = 1) (hb : d76457 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75647, d76457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75647, d76457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75648 q = 1) (hb : d76458 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75648, d76458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75648, d76458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d75649 q = 1) (hb : d76464 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75649, d76464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75649, d76464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7498 (p : Pattern) (ha : d5377 p = 1) (hb : d74103 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238 q = 1) (hb : d52056 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d52056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25 q ha hb
    | true =>
      simp only [d238, d52056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239 q = 1) (hb : d52057 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d52057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d52057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5374 q = 1) (hb : d74100 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5374, d74100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5374, d74100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5375 q = 1) (hb : d74101 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5375, d74101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5375, d74101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5376 q = 1) (hb : d74102 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5376, d74102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5376, d74102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5377 q = 1) (hb : d74103 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5377, d74103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5377, d74103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7499 (p : Pattern) (ha : d75660 p = 1) (hb : d76473 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51935 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5378 q = 1) (hb : d75655 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5378, d75655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7498 q ha hb
    | true =>
      simp only [d5378, d75655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5379 q = 1) (hb : d75656 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5379, d75656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5379, d75656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
    | true =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85 q = 1) (hb : d51937 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, d51937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85, d51937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d75657 q = 1) (hb : d76470 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75657, d76470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d75657, d76470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d75658 q = 1) (hb : d76471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75658, d76471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75658, d76471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75659 q = 1) (hb : d76472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75659, d76472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75659, d76472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d75660 q = 1) (hb : d76473 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75660, d76473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75660, d76473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
end NetHack.Soko22Hazard87
